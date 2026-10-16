/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Sum32.Pointer
import EDSL.X86.CodeCheck
import EDSL.Audit

namespace EDSL.Tests.Sum32Pointer
open X86 Sum32
set_option maxRecDepth 100000

-- The first window is the observed final GCC13 pointer/count .text.
-- The second uses MOV-zero and commutes the two updates. Its changed header
-- offset also checks that the loop proof does not depend on the GCC layout.
def bytes : Bool → List Byte
  | false => [0x31, 0xc0, 0x48, 0x85, 0xf6, 0x74, 0x0b, 0x03, 0x07,
      0x48, 0xff, 0xce, 0x48, 0x83, 0xc7, 0x04, 0xeb, 0xf0, 0xc3]
  | true => [0xb8, 0, 0, 0, 0, 0x48, 0x85, 0xf6, 0x74, 0x0b, 0x03, 0x07,
      0x48, 0x83, 0xc7, 0x04, 0x48, 0xff, 0xce, 0xeb, 0xf0, 0xc3]

def plan : Bool → Plan
  | false => ⟨.pointerCount, [⟨0, .xorSelf32 .rax⟩], 2, ⟨5, 11⟩, 7,
      [⟨9, .dec64 .rsi⟩, ⟨12, .addImm64 .rdi 4⟩], ⟨16, 240⟩, 18⟩
  | true => ⟨.pointerCount, [⟨0, .legacy (.mov32 .rax 0)⟩], 5, ⟨8, 11⟩, 10,
      [⟨12, .addImm64 .rdi 4⟩, ⟨16, .dec64 .rsi⟩], ⟨19, 240⟩, 21⟩

theorem valid (commuted : Bool) : Valid (bytes commuted) (plan commuted) :=
  checkPlan_sound (by cases commuted <;> decide)

-- Only the two data elements and the complete return slot are readable.
-- In particular the one-past input address is unmapped and nothing is writable.
def memory (commuted : Bool) : Memory where
  read address :=
    if 4096 ≤ address.toNat ∧ address.toNat < 4096 + (bytes commuted).length then
      (bytes commuted)[address.toNat - 4096]?
    else if 12288 ≤ address.toNat ∧ address.toNat < 12296 then
      [0xff, 0xff, 0xff, 0xff, 2, 0, 0, 0][address.toNat - 12288]?
    else if 32768 ≤ address.toNat ∧ address.toNat < 32776 then
      [0, 0x20, 0, 0, 0, 0, 0, 0][address.toNat - 32768]?
    else none
  executable address := decide (4096 ≤ address.toNat ∧
    address.toNat < 4096 + (bytes commuted).length)

def headerState (commuted : Bool) (pointer : Word) (count : Nat) (accumulator : BitVec 32) : State where
  registers register := match register with
    | .rax => accumulator.setWidth 64
    | .rsi => BitVec.ofNat 64 count
    | .rdi => pointer
    | .rsp => 32768
    | _ => 0xfedcba9876543210
  rip := 4096 + BitVec.ofNat 64 (plan commuted).header
  flags := 0x602
  memory := memory commuted

theorem current_code (commuted : Bool) : CodeAt (memory commuted) 4096 (bytes commuted) :=
  checkCode_sound _ _ _ (by cases commuted <;> decide)

theorem empty_header (commuted : Bool) (pointer : Word) (accumulator : BitVec 32) :
    PointerHeader (bytes commuted) (plan commuted) 4096
      (headerState commuted pointer 0 accumulator) [] accumulator 8192 := by
  refine ⟨⟨current_code commuted, rfl, rfl, ?_, by decide,
    by change canonical ((32768 : Word) + 8) = true; decide⟩,
    ArrayAt.nil _ _, rfl, by decide⟩
  change readWord (memory commuted) 32768 = .ok 8192
  cases commuted <;> rfl

-- This proves enabledness and the exact trace for EVERY unused pointer, prefix
-- accumulator and AF stream, including a noncanonical, unreadable pointer.
theorem empty_all_choices (commuted : Bool) (pointer : Word) (accumulator : BitVec 32)
    (choices : Sequential.Choices) :
    ∃ result, Sequential.Executes choices (headerState commuted pointer 0 accumulator) result ∧
      result.state.registers .rax = accumulator.setWidth 64 ∧
      result.instructions = 3 ∧ result.reads = [⟨.stack, 32768, 8⟩] := by
  obtain ⟨result, execution, post, cost, reads⟩ := pointer_loop (valid commuted)
    (by cases commuted <;> rfl) (empty_header commuted pointer accumulator) choices
  exact ⟨result, execution, by simpa using post.value, cost, reads⟩

theorem wrapping_header (commuted : Bool) :
    PointerHeader (bytes commuted) (plan commuted) 4096
      (headerState commuted 12288 2 0) [0xffffffff, 2] 0 8192 := by
  refine ⟨⟨current_code commuted, rfl, rfl, ?_, by decide,
    by change canonical ((32768 : Word) + 8) = true; decide⟩, ?_, rfl, by decide⟩
  · change readWord (memory commuted) 32768 = .ok 8192
    cases commuted <;> rfl
  · intro index value present
    match index with
    | 0 | 1 => simp at present; subst value; cases commuted <;> rfl
    | index + 2 => simp at present

-- The independent expected sum is 1 modulo 2^32. Both legal update orders
-- have the same two reads and do not touch the unmapped one-past address.
theorem wrapping_all_choices (commuted : Bool) (choices : Sequential.Choices) :
    ∃ result, Sequential.Executes choices (headerState commuted 12288 2 0) result ∧
      result.state.registers .rax = 1 ∧ result.state.rip = 8192 ∧
      result.state.registers .rsp = 32776 ∧ result.instructions = 15 ∧
      result.reads = [⟨.data, 12288, 4⟩, ⟨.data, 12292, 4⟩, ⟨.stack, 32768, 8⟩] := by
  obtain ⟨result, execution, post, cost, reads⟩ := pointer_loop (valid commuted)
    (by cases commuted <;> rfl) (wrapping_header commuted) choices
  exact ⟨result, execution, post.value, post.returnAddress, post.stackPointer, cost, reads⟩

def observe (choices : Sequential.Choices) (fuel : Nat) (initial : State) :
    Option (Word × Word × Word × Word × Nat × List Sequential.Read) := do
  let result ← (Sequential.run choices fuel initial).toOption
  return (result.state.registers .rax, result.state.flags, result.state.rip,
    result.state.registers .rsp, result.instructions, result.reads)

-- TEST on the final zero count consumes choice 12, after two six-step bodies.
-- DF and IF survive. This also detects reuse of the initial AF choice.
example (commuted : Bool) :
    observe (fun index => decide (index = 12)) 15 (headerState commuted 12288 2 0) =
      some (1, 0x656, 8192, 32776, 15,
        [⟨.data, 12288, 4⟩, ⟨.data, 12292, 4⟩, ⟨.stack, 32768, 8⟩]) := by
  cases commuted <;> rfl

-- The loop theorem starts at its header: a nonzero prefix is retained, and
-- an unreadable noncanonical input address is harmless when RSI is zero.
example (commuted : Bool) :
    observe (fun _ => false) 3 (headerState commuted 0x800000000000 0 0x80000001) =
      some (0x80000001, 0x646, 8192, 32776, 3, [⟨.stack, 32768, 8⟩]) := by
  cases commuted <;> rfl

end EDSL.Tests.Sum32Pointer

#audit_edsl
