/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.ByteEquality

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.ByteEquality
open X86 X86.Sequential BufferCall Grading.ByteEquality

/-- An equal nonempty input returns one in AL while dirty bits survive in
both the high 32 bits and the remaining three bytes of low32 RAX. -/
theorem equal_complete_lists_dirty_upper56 :
    spec.result ⟨0x100000001, 0x200000003, [0, 0x80, 0xff, 0x42],
      [0, 0x80, 0xff, 0x42]⟩ 0xfedcba9876543201 ∧
      (0xfedcba9876543201 : Word).setWidth 32 ≠ 1 := by
  exact ⟨result_of_equal rfl (by decide), by decide⟩

/-- The final byte is part of equality; a shared initial segment is insufficient. -/
theorem unequal_complete_lists_dirty_upper56 :
    spec.result ⟨0x100000001, 0x200000003, [0, 0x80, 0xff, 0x42],
      [0, 0x80, 0xff, 0x43]⟩ 0xdeadbeef12345600 ∧
      ¬spec.result ⟨0x100000001, 0x200000003, [0, 0x80, 0xff, 0x42],
        [0, 0x80, 0xff, 0x43]⟩ 0xdeadbeef12345601 := by
  have different : ([0, 0x80, 0xff, 0x42] : List Byte) ≠ [0, 0x80, 0xff, 0x43] := by
    decide
  constructor
  · exact result_of_mismatch different (by decide)
  · rw [result_mismatch different]
    decide

/-- Values with the eighth bit set remain full bytes in the equality contract. -/
theorem high_bit_mismatch :
    spec.result ⟨0, 0, [0x80, 0xff], [0, 0x7f]⟩ 0x8877665544332200 ∧
      ¬spec.result ⟨0, 0, [0x80, 0xff], [0, 0x7f]⟩ 1 := by
  have different : ([0x80, 0xff] : List Byte) ≠ [0, 0x7f] := by decide
  exact ⟨result_of_mismatch different (by decide), by
    rw [result_mismatch different]
    decide⟩

/-- Merely testing AL for nonzero would incorrectly admit this return. -/
theorem noncanonical_two_rejected (input : Input) :
    ¬spec.result input 0xffffffffffffff02 :=
  result_rejects_noncanonical (by decide) (by decide)

theorem mismatch_after_arbitrary_common_prefix (front leftTail rightTail : List Byte)
    (a b : Byte) (different : a ≠ b) (actual : Word)
    (returned : returnValue actual = 0) :
    spec.result ⟨0, 0, front ++ a :: leftTail, front ++ b :: rightTail⟩ actual := by
  apply result_at_mismatch (index := front.length) (a := a) (b := b)
  · simp
  · simp
  · exact different
  · exact returned

/-- Truncating zip to its shorter input cannot justify Boolean equality. -/
theorem unequal_extents_not_admitted :
    ¬spec.domain ⟨0, 0, [0x80], [0x80, 0]⟩ ∧
      ¬spec.result ⟨0, 0, [0x80], [0x80, 0]⟩ 1 := by
  constructor
  · intro domain
    have lengths := domain.1
    cases lengths
  · rw [result_mismatch (by decide)]
    decide

theorem empty_arbitrary_bases_dirty_upper56 (leftBase rightBase : Word) :
    spec.result ⟨leftBase, rightBase, [], []⟩ 0xffffffffffff0001 ∧
      ¬spec.result ⟨leftBase, rightBase, [], []⟩ 0xffffffffffff0000 := by
  rw [result_empty, result_empty]
  decide

/-- The original code/caller contract suffices for arbitrary empty addresses
and arbitrary loan IDs; no positive DATA operand receives authority. -/
theorem empty_original_resources_no_data (shared : OS.Borrowing.State)
    (call : OS.CallResources.Call) (original : OS.CallResources.Contract call shared)
    (leftBase rightBase : Word) (unused : Buffer → Nat) :
    ResourceContract (⟨shared, call, ⟨leftBase, rightBase, [], []⟩, unused⟩ : Resources spec)
        shared ∧
      ∀ read, ¬DataRead (spec.buffers ⟨leftBase, rightBase, [], []⟩) read :=
  ⟨empty_resources shared call original leftBase rightBase unused,
    empty_no_data leftBase rightBase⟩

/-- Even unrelated live authority cannot add DATA reads to an empty call. -/
theorem empty_foreign_authority_cannot_add_data (shared : OS.Borrowing.State)
    (call : OS.CallResources.Call) (leftBase rightBase address : Word)
    (unused : Buffer → Nat) (width : Nat) :
    ¬ReadAllowed (⟨shared, call, ⟨leftBase, rightBase, [], []⟩, unused⟩ : Resources spec)
      ⟨.data, address, width⟩ := by
  rintro (stack | data)
  · cases stack.1
  · exact empty_no_data leftBase rightBase _ data.1

/-- The original two-loan resource bridge transfers without any result or
machine-execution premise, including compatible overlapping buffers. -/
theorem original_two_loan_bridge (resource : Resources Grading.ByteComparison.spec)
    (shared : OS.Borrowing.State) (current : ResourceContract resource shared) :
    ResourceContract
      (⟨resource.shared, resource.call, resource.value, resource.inputLoan⟩ : Resources spec)
      shared :=
  (resourceContract_comparison_iff _ _).mpr current

/-- Initial admission also preserves the original call, snapshots and every
ABI binding, without requiring either task's return relation in advance. -/
theorem original_pre_bridge (bytes : List Byte)
    (resource : Resources Grading.ByteComparison.spec) (initial : State)
    (pre : ResourcePre Grading.ByteComparison.spec bytes resource initial) :
    ResourcePre spec bytes
      ⟨resource.shared, resource.call, resource.value, resource.inputLoan⟩ initial :=
  (resourcePre_comparison_iff _ _ _).mpr pre

/-- A readable right buffer still needs its original exact live loan. -/
theorem missing_right_loan_rejected (resource : Resources spec) (shared : OS.Borrowing.State)
    (nonempty : resource.value.right ≠ [])
    (missing : ¬OS.Threads.HasLoan shared resource.call.worker
      (resource.inputLoan (rightBuffer resource.value)) (rightBuffer resource.value).region) :
    ¬ResourceContract resource shared := by
  intro current
  exact missing (((resourceContract_iff _ _).mp current).2.2.2.2 nonempty)

/-- Argument admission retains every bit of both pointers and the count. -/
theorem original_full64_bindings (input : Input) (initial : State)
    (bound : Bound spec input initial) :
    initial.registers .rdi = input.leftBase ∧
      initial.registers .rsi = input.rightBase ∧
      initial.registers .rdx = BitVec.ofNat 64 input.left.length :=
  (bound_iff input initial).mp bound

end EDSL.Tests.ByteEquality
