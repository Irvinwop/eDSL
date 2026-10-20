/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.ByteComparisonBodies
import Lean

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.ByteComparisonBodies
open X86 X86.Sequential Grading.ByteComparison Corpus.V1

/-- An actual-execution consequence of the generated policy, for every
admitted empty call, arbitrary pointers, initial state and AF stream. Original
STACK8 authority suffices; neither empty data-loan selector can be consulted. -/
theorem empty_no_data (compiler : ByteComparisonWindows.Compiler)
    (input : BufferCall.Invocation spec) (initial : State)
    (pre : BufferCall.Pre spec (ByteComparisonWindows.bytes compiler) input initial)
    (emptyLeft : input.value.left = []) (emptyRight : input.value.right = [])
    (choices : Choices) :
    ∃ result, Sequential.Executes choices initial result ∧
      (result.state.registers .rax).setWidth 32 = 0 ∧
      BufferCall.Post spec input initial result.state ∧
      ∀ read ∈ result.reads, PureCall.RawRead initial read := by
  have executions := (Corpus.V1.ByteComparisonBodies.raw compiler input initial pre).1
  have policy := Corpus.V1.ByteComparisonBodies.empty_raw_policy compiler input initial pre emptyLeft emptyRight
  obtain ⟨result, execution, post⟩ := executions choices
  have returned := result_low32_zero_iff_equal post.result
  refine ⟨result, execution, returned.mpr (emptyLeft.trans emptyRight.symm), post, ?_⟩
  intro read member
  obtain ⟨_, _, _, _, _, _, _, _, _, allowed, _⟩ :=
    Grading.ReadOnlyPolicy.read_origin policy execution member
  exact allowed

/- Small regression executions use the actual decoder, DATA1 checks and
production executor. Only the exact code, original caller and listed data are
mapped. The fixed test fuel is absent from every universal admission contract. -/
private def memory (compiler : ByteComparisonWindows.Compiler) (leftBase rightBase : Word)
    (left right : List Byte) : Memory where
  read address :=
    if 0x1000 ≤ address.toNat ∧ address.toNat < 0x1000 + (ByteComparisonWindows.bytes compiler).length then
      (ByteComparisonWindows.bytes compiler)[address.toNat - 0x1000]?
    else if 0x2000 ≤ address.toNat ∧ address.toNat < 0x2008 then
      ([0, 0x30, 0, 0, 0, 0, 0, 0] : List Byte)[address.toNat - 0x2000]?
    else if leftBase.toNat ≤ address.toNat ∧ address.toNat < leftBase.toNat + left.length then
      left[address.toNat - leftBase.toNat]?
    else if rightBase.toNat ≤ address.toNat then right[address.toNat - rightBase.toNat]?
    else none
  executable address := decide (0x1000 ≤ address.toNat ∧
    address.toNat < 0x1000 + (ByteComparisonWindows.bytes compiler).length)

private def initial (compiler : ByteComparisonWindows.Compiler) (leftBase rightBase : Word)
    (left right : List Byte) (count : Nat) : State where
  registers register := if register = .rsp then 0x2000
    else if register = .rdi then leftBase
    else if register = .rsi then rightBase
    else if register = .rdx then BitVec.ofNat 64 count
    else if register = .rax then 0xfedcba9876543210
    else if register = .rcx then 0xdeadbeef87654321
    else if register = .r8 then 0x9abcdef012345678
    else 0xfedcba9876543210
  rip := 0x1000
  flags := 0xfedcba987654246a
  memory := memory compiler leftBase rightBase left right

private def observed (compiler : ByteComparisonWindows.Compiler) (leftBase rightBase : Word)
    (left right : List Byte) (count : Nat) (af : Bool) : Option (Int × List Read × Word × Word) :=
  (Sequential.run (fun _ => af) 96 (initial compiler leftBase rightBase left right count)).toOption.map
    (fun result => (returnValue (result.state.registers .rax), result.reads,
      result.state.registers .rsp, result.state.rip))

/-- Unsigned high-byte order and swapped operands expose signed-byte CMP,
reversed subtraction, missing zero extension and dirty scratch high bits. -/
theorem high_bytes_both_orders (compiler : ByteComparisonWindows.Compiler) (af : Bool) :
    observed compiler 0x4001 0x5003 [0x80] [0x7f] 1 af =
      some (1, [⟨.data, 0x4001, 1⟩, ⟨.data, 0x5003, 1⟩, ⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000) ∧
    observed compiler 0x4001 0x5003 [0x7f] [0x80] 1 af =
      some (-1, [⟨.data, 0x4001, 1⟩, ⟨.data, 0x5003, 1⟩, ⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000) := by
  cases compiler <;> cases af <;> decide +kernel

/-- Distinct dirty scratch words prevent stale upper bits from cancelling in
subtraction. This observes the actual MOVZX/SUB32 zero-extension effects,
including upper32 bits that the independent C return contract leaves free. -/
theorem dirty_scratch_zero_extend (compiler : ByteComparisonWindows.Compiler) (af : Bool) :
    ((Sequential.run (fun _ => af) 96
      (initial compiler 0x4001 0x5003 [0x80] [0x7f] 1)).toOption.map
        (fun result => (result.state.registers .rax, result.state.registers .r8))) =
      some (1, 0x7f) := by
  cases compiler <;> cases af <;> decide +kernel

/-- The first unequal pair, including at the final guarded byte, determines
the sign. Reading after that pair or widening either read would fault. -/
theorem late_unequal_guard (compiler : ByteComparisonWindows.Compiler) (af : Bool) :
    observed compiler 0x4001 0x5003 [0xff, 0x80, 0] [0xff, 0x80, 0xff] 3 af =
      some (-255, [⟨.data, 0x4001, 1⟩, ⟨.data, 0x5003, 1⟩,
        ⟨.data, 0x4002, 1⟩, ⟨.data, 0x5004, 1⟩,
        ⟨.data, 0x4003, 1⟩, ⟨.data, 0x5005, 1⟩, ⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000) := by
  cases compiler <;> cases af <;> decide +kernel

theorem first_pair_stops (compiler : ByteComparisonWindows.Compiler) (af : Bool) :
    observed compiler 0x4001 0x5003 [0xff, 0] [0, 0xff] 2 af =
      some (255, [⟨.data, 0x4001, 1⟩, ⟨.data, 0x5003, 1⟩, ⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000) := by
  cases compiler <;> cases af <;> decide +kernel

/-- Exhaustion requires n complete equal pairs and no neighbor reads. -/
theorem equal_guard (compiler : ByteComparisonWindows.Compiler) (af : Bool) :
    observed compiler 0x4001 0x5003 [0, 0x80] [0, 0x80] 2 af =
      some (0, [⟨.data, 0x4001, 1⟩, ⟨.data, 0x5003, 1⟩,
        ⟨.data, 0x4002, 1⟩, ⟨.data, 0x5004, 1⟩, ⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000) := by
  cases compiler <;> cases af <;> decide +kernel

/-- The count test observes all 64 bits. Only a first unequal pair is needed
for this decoder/executor regression; it is not a large snapshot admission. -/
theorem full_count (compiler : ByteComparisonWindows.Compiler) (af : Bool) :
    observed compiler 0x4001 0x5003 [0x80] [0x7f] (2^32) af =
      some (1, [⟨.data, 0x4001, 1⟩, ⟨.data, 0x5003, 1⟩, ⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000) := by
  cases compiler <;> cases af <;> decide +kernel

theorem empty_unmapped_both (compiler : ByteComparisonWindows.Compiler) (af : Bool) :
    observed compiler 0x800000000000 0x800000000001 [] [] 0 af =
      some (0, [⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000) := by
  cases compiler <;> cases af <;> decide +kernel

/-- Compatible overlap at unaligned addresses retains the same actual RAM
bytes; the second pair is the first unequal one. -/
theorem overlapping_inputs (compiler : ByteComparisonWindows.Compiler) (af : Bool) :
    observed compiler 0x4001 0x4002 [0x80, 0x80, 0x7f] [0x80, 0x7f, 0x55] 3 af =
      some (1, [⟨.data, 0x4001, 1⟩, ⟨.data, 0x4002, 1⟩,
        ⟨.data, 0x4002, 1⟩, ⟨.data, 0x4003, 1⟩, ⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000) := by
  cases compiler <;> cases af <;> decide +kernel

theorem identical_inputs (compiler : ByteComparisonWindows.Compiler) (af : Bool) :
    observed compiler 0x4001 0x4001 [0, 0x80] [0, 0x80] 2 af =
      some (0, [⟨.data, 0x4001, 1⟩, ⟨.data, 0x4001, 1⟩,
        ⟨.data, 0x4002, 1⟩, ⟨.data, 0x4002, 1⟩, ⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000) := by
  cases compiler <;> cases af <;> decide +kernel

theorem caller_alias (compiler : ByteComparisonWindows.Compiler) (af : Bool) :
    observed compiler 0x2000 0x2000 [] [] 2 af =
      some (0, [⟨.data, 0x2000, 1⟩, ⟨.data, 0x2000, 1⟩,
        ⟨.data, 0x2001, 1⟩, ⟨.data, 0x2001, 1⟩, ⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000) := by
  cases compiler <;> cases af <;> decide +kernel

theorem code_alias (compiler : ByteComparisonWindows.Compiler) (af : Bool) :
    observed compiler 0x1000 0x1000 [] [] 1 af =
      some (0, [⟨.data, 0x1000, 1⟩, ⟨.data, 0x1000, 1⟩, ⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000) := by
  cases compiler <;> cases af <;> decide +kernel

theorem full_address (compiler : ByteComparisonWindows.Compiler) (af : Bool) :
    observed compiler 0xffff800000004001 0xffff800000005003 [0x80] [0x7f] 1 af =
      some (1, [⟨.data, 0xffff800000004001, 1⟩, ⟨.data, 0xffff800000005003, 1⟩,
        ⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000) := by
  cases compiler <;> cases af <;> decide +kernel

end EDSL.Tests.ByteComparisonBodies

elab "#audit_byte_comparison_bodies" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := #[``EDSL.X86.VCGen.ByteComparison.view,
    ``EDSL.X86.VCGen.ByteComparison.commonFrame_iff,
    ``EDSL.X86.VCGen.ByteComparison.CommonFrame.refl,
    ``EDSL.X86.VCGen.ByteComparison.CommonFrame.rsp,
    ``EDSL.X86.VCGen.ByteComparison.CommonFrame.rdi,
    ``EDSL.X86.VCGen.ByteComparison.CommonFrame.rsi,
    ``EDSL.X86.VCGen.ByteComparison.CommonFrame.rdx,
    ``EDSL.X86.VCGen.ByteComparison.saved_different,
    ``EDSL.X86.VCGen.ByteComparison.same_length,
    ``EDSL.X86.VCGen.ByteComparison.count_small,
    ``EDSL.X86.VCGen.ByteComparison.count_nat,
    ``EDSL.X86.VCGen.ByteComparison.left_argument,
    ``EDSL.X86.VCGen.ByteComparison.right_argument,
    ``EDSL.X86.VCGen.ByteComparison.count_argument,
    ``EDSL.X86.VCGen.ByteComparison.read_byte,
    ``EDSL.X86.VCGen.ByteComparison.read_pair,
    ``EDSL.X86.VCGen.ByteComparison.next_nat,
    ``EDSL.X86.VCGen.ByteComparison.next_rank,
    ``EDSL.X86.VCGen.ByteComparison.advance,
    ``EDSL.X86.VCGen.ByteComparison.finish_bound,
    ``EDSL.X86.VCGen.ByteComparison.finish_hit,
    ``EDSL.X86.VCGen.ByteComparison.sub_return,
    ``EDSL.Corpus.V1.ByteComparisonBodies.gcc_valid,
    ``EDSL.Corpus.V1.ByteComparisonBodies.clang_valid,
    ``EDSL.Corpus.V1.ByteComparisonBodies.gccAnnotations,
    ``EDSL.Corpus.V1.ByteComparisonBodies.clangAnnotations,
    ``EDSL.Corpus.V1.ByteComparisonBodies.valid,
    ``EDSL.Corpus.V1.ByteComparisonBodies.annotations,
    ``EDSL.Corpus.V1.ByteComparisonBodies.entry_invariant,
    ``EDSL.Corpus.V1.ByteComparisonBodies.generated,
    ``EDSL.Corpus.V1.ByteComparisonBodies.raw,
    ``EDSL.Corpus.V1.ByteComparisonBodies.empty_raw_policy,
    ``EDSL.Corpus.V1.ByteComparisonBodies.semantics,
    ``EDSL.Corpus.V1.ByteComparisonBodies.dynamic_bound,
    ``EDSL.Tests.ByteComparisonBodies.empty_no_data,
    ``EDSL.Tests.ByteComparisonBodies.high_bytes_both_orders,
    ``EDSL.Tests.ByteComparisonBodies.dirty_scratch_zero_extend,
    ``EDSL.Tests.ByteComparisonBodies.late_unequal_guard,
    ``EDSL.Tests.ByteComparisonBodies.first_pair_stops,
    ``EDSL.Tests.ByteComparisonBodies.equal_guard,
    ``EDSL.Tests.ByteComparisonBodies.full_count,
    ``EDSL.Tests.ByteComparisonBodies.empty_unmapped_both,
    ``EDSL.Tests.ByteComparisonBodies.overlapping_inputs,
    ``EDSL.Tests.ByteComparisonBodies.identical_inputs,
    ``EDSL.Tests.ByteComparisonBodies.caller_alias,
    ``EDSL.Tests.ByteComparisonBodies.code_alias,
    ``EDSL.Tests.ByteComparisonBodies.full_address]
  for name in names do
    for dependency in ← Lean.collectAxioms name do
      unless allowed.contains dependency do
        throwError "{name} depends on unapproved axiom {dependency}"
    Lean.logInfo m!"Allowed named audit passed: {name}"

#print axioms EDSL.Corpus.V1.ByteComparisonBodies.semantics
#print axioms EDSL.Corpus.V1.ByteComparisonBodies.dynamic_bound
#print axioms EDSL.Corpus.V1.ByteComparisonBodies.empty_raw_policy
#print axioms EDSL.Tests.ByteComparisonBodies.empty_no_data
#audit_byte_comparison_bodies
