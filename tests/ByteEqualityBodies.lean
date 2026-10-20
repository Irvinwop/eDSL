/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.ByteEqualityBodies
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.ByteEqualityBodies
open X86 X86.Sequential Grading.ByteEquality Corpus.V1

/-- The universal generated policy excludes every DATA observation on an
admitted empty call, even with arbitrary bases, scratch bits and choices. -/
theorem empty_no_data (compiler : ByteEqualityWindows.Compiler)
    (input : BufferCall.Invocation spec) (initial : State)
    (pre : BufferCall.Pre spec (ByteEqualityWindows.bytes compiler) input initial)
    (emptyLeft : input.value.left = []) (emptyRight : input.value.right = [])
    (choices : Choices) :
    ∃ result, Sequential.Executes choices initial result ∧
      (result.state.registers .rax).setWidth 8 = 1 ∧
      BufferCall.Post spec input initial result.state ∧
      ∀ read ∈ result.reads, PureCall.RawRead initial read := by
  obtain ⟨result,execution,post⟩ := (Corpus.V1.ByteEqualityBodies.raw compiler input initial pre).1 choices
  have policy := Corpus.V1.ByteEqualityBodies.empty_raw_policy compiler input initial pre emptyLeft emptyRight
  refine ⟨result,execution,(result_low8_one_iff_equal post.result).mpr
    (emptyLeft.trans emptyRight.symm),post,?_⟩
  intro read member
  obtain ⟨_,_,_,_,_,_,_,_,_,allowed,_⟩ := Grading.ReadOnlyPolicy.read_origin policy execution member
  exact allowed

/-- Only exact code, original caller and explicit DATA bytes are mapped.
Execution tests use finite fuel; that fuel is absent from the universal Pre. -/
private def memory (compiler : ByteEqualityWindows.Compiler) (leftBase rightBase : Word)
    (left right : List Byte) : Memory where
  read address :=
    if 0x1000 ≤ address.toNat ∧ address.toNat < 0x1000 + (ByteEqualityWindows.bytes compiler).length then
      (ByteEqualityWindows.bytes compiler)[address.toNat - 0x1000]?
    else if 0x2000 ≤ address.toNat ∧ address.toNat < 0x2008 then
      ([0,0x30,0,0,0,0,0,0] : List Byte)[address.toNat - 0x2000]?
    else if leftBase.toNat ≤ address.toNat ∧ address.toNat < leftBase.toNat + left.length then
      left[address.toNat - leftBase.toNat]?
    else if rightBase.toNat ≤ address.toNat then right[address.toNat - rightBase.toNat]?
    else none
  executable address := decide (0x1000 ≤ address.toNat ∧
    address.toNat < 0x1000 + (ByteEqualityWindows.bytes compiler).length)
  writable address := address == 0x7777

private def initial (compiler : ByteEqualityWindows.Compiler) (leftBase rightBase : Word)
    (left right : List Byte) (count : Nat) : State where
  registers register := if register = .rsp then 0x2000
    else if register = .rdi then leftBase else if register = .rsi then rightBase
    else if register = .rdx then BitVec.ofNat 64 count
    else if register = .rax then 0xfedcba9876543210
    else if register = .rcx then 0xdeadbeef87654321
    else if register = .r8 then 0x9abcdef012345678
    else 0xfedcba9876543210
  rip := 0x1000
  flags := 0xfedcba987654246a
  memory := memory compiler leftBase rightBase left right

private def observed (compiler : ByteEqualityWindows.Compiler) (leftBase rightBase : Word)
    (left right : List Byte) (count : Nat) (af : Bool) : Option (Byte × Nat × Word × Word) :=
  (Sequential.run (fun _ => af) 96 (initial compiler leftBase rightBase left right count)).toOption.map
    (fun result => ((result.state.registers .rax).setWidth 8,
      (result.reads.filter (fun read => read.kind == .data)).length,
      result.state.registers .rsp,result.state.rip))

/-- Complete equal extents require canonical Boolean one; first and final
unequal bytes require zero and stop after that pair, without neighbor reads. -/
theorem complete_boolean_cases (compiler : ByteEqualityWindows.Compiler) (af : Bool) :
    observed compiler 0x4001 0x5003 [0,0x80,0xff] [0,0x80,0xff] 3 af =
      some (1,6,0x2008,0x3000) ∧
    observed compiler 0x4001 0x5003 [0xff,0,0] [0,0xff,0xff] 3 af =
      some (0,2,0x2008,0x3000) ∧
    observed compiler 0x4001 0x5003 [0xff,0x80,0] [0xff,0x80,0xff] 3 af =
      some (0,6,0x2008,0x3000) := by
  cases compiler <;> cases af <;> decide +kernel

/-- B001 on Clang's empty path must preserve all upper56 RAX bits. Both empty
pointers lie in the canonical hole, so any DATA read would fail. -/
theorem empty_dirty_upper56 (af : Bool) :
    observed .defaultClang 0x800000000000 0x800000000001 [] [] 0 af =
      some (1,0,0x2008,0x3000) ∧
    ((Sequential.run (fun _ => af) 96
      (initial .defaultClang 0x800000000000 0x800000000001 [] [] 0)).toOption.map
        (fun result => result.state.registers .rax)) = some 0xfedcba9876543201 := by
  cases af <;> decide +kernel

theorem empty_gcc_no_data (af : Bool) :
    observed .defaultGCC 0x800000000000 0x800000000001 [] [] 0 af =
      some (1,0,0x2008,0x3000) := by cases af <;> decide +kernel

/-- Full64 count testing and full64 addresses remain observable. This large
count case is a first-mismatch execution regression, not a huge admitted snapshot. -/
theorem full_width_guard (compiler : ByteEqualityWindows.Compiler) (af : Bool) :
    observed compiler 0xffff800000004001 0xffff800000005003 [0x80] [0x7f] 1 af =
      some (0,2,0x2008,0x3000) ∧
    observed compiler 0x4001 0x5003 [0x80] [0x7f] (2^32) af =
      some (0,2,0x2008,0x3000) := by
  cases compiler <;> cases af <;> decide +kernel

/-- These overlapping descriptions agree on every shared byte in the same
actual Memory. No disjointness premise may be added by a read rule. -/
theorem compatible_aliases (compiler : ByteEqualityWindows.Compiler) (af : Bool) :
    observed compiler 0x4001 0x4001 [0,0x80] [0,0x80] 2 af =
      some (1,4,0x2008,0x3000) ∧
    observed compiler 0x4001 0x4002 [0x80,0x80,0x7f] [0x80,0x7f,0x55] 3 af =
      some (0,4,0x2008,0x3000) := by
  cases compiler <;> cases af <;> decide +kernel

/-- A missing right byte is a real read failure, not a Boolean mismatch or
permission supplied by the independent code mapping. -/
theorem missing_right_fails (compiler : ByteEqualityWindows.Compiler) (af : Bool) :
    (match Sequential.run (fun _ => af) 96
      (initial compiler 0x4001 0x5003 [0x80] [] 1) with
      | .error (.inaccessibleData 0x5003) => true
      | _ => false) = true := by
  cases compiler <;> cases af <;> decide +kernel

/-- Explicit wider admission must leave the original default limit intact. -/
theorem clang_default_rejects :
    CFG.analyze (ByteEqualityWindows.bytes .defaultClang) = .error .byteLimit := rfl

end EDSL.Tests.ByteEqualityBodies

#print axioms EDSL.Corpus.V1.ByteEqualityWindows.checked
#print axioms EDSL.Corpus.V1.ByteEqualityBodies.semantics
#print axioms EDSL.Corpus.V1.ByteEqualityBodies.dynamic_bound
#print axioms EDSL.Tests.ByteEqualityBodies.empty_no_data
#audit_edsl
