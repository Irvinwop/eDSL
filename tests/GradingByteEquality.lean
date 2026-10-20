/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.BufferTask
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.GradingByteEquality
open X86 X86.Sequential BufferCall Grading.BufferTask

/-- Fixed registration observes only AL, including for bytes after a NUL and
with dirty bits in both the high32 and the rest of low32 RAX. -/
theorem registered_equal_dirty_upper56 :
    (registeredSpec .equalBytes).result
      ⟨0x100000001, 0x200000003, [0, 0x80, 0xff, 0x42], [0, 0x80, 0xff, 0x42]⟩
      0xfedcba9876543201 ∧
      ¬(registeredSpec .equalBytes).result
        ⟨0x100000001, 0x200000003, [0, 0x80, 0xff, 0x42], [0, 0x80, 0xff, 0x42]⟩
        0xfedcba9876543200 := by
  simp only [registeredSpec, Grading.ByteEquality.spec, Grading.ByteEquality.Result,
    Grading.ByteComparison.spec]
  decide +kernel

/-- A final-byte mismatch in admitted equal-length inputs requires AL=0.
Neither the initial NUL nor the common high-byte prefix ends the comparison. -/
theorem registered_unequal_same_length :
    (registeredSpec .equalBytes).domain
      ⟨0x100000001, 0x200000003, [0, 0x80, 0xff, 0x42], [0, 0x80, 0xff, 0x43]⟩ ∧
      (registeredSpec .equalBytes).result
        ⟨0x100000001, 0x200000003, [0, 0x80, 0xff, 0x42], [0, 0x80, 0xff, 0x43]⟩
        0xdeadbeef12345600 ∧
      ¬(registeredSpec .equalBytes).result
        ⟨0x100000001, 0x200000003, [0, 0x80, 0xff, 0x42], [0, 0x80, 0xff, 0x43]⟩
        0xdeadbeef12345601 := by
  simp only [registeredSpec, Grading.ByteEquality.spec, Grading.ByteEquality.Result,
    Grading.ByteComparison.spec]
  decide +kernel

/-- Boolean truth is canonical, rather than any nonzero byte. -/
theorem registered_noncanonical_two_rejected (input : Grading.ByteEquality.Input) :
    ¬(registeredSpec .equalBytes).result input 0xffffffffffffff02 :=
  Grading.ByteEquality.result_rejects_noncanonical (by decide) (by decide)

/-- The two fixed IDs retain different answers on every equal list. -/
theorem registered_equality_differs_from_lexicographic (leftBase rightBase : Word)
    (values : List Byte) :
    (registeredSpec .equalBytes).result ⟨leftBase, rightBase, values, values⟩ 1 ∧
      ¬(registeredSpec .equalBytes).result ⟨leftBase, rightBase, values, values⟩ 0 ∧
      (registeredSpec .lexicographicBytes).result ⟨leftBase, rightBase, values, values⟩ 0 ∧
      ¬(registeredSpec .lexicographicBytes).result ⟨leftBase, rightBase, values, values⟩ 1 := by
  refine ⟨Grading.ByteEquality.result_of_equal rfl rfl, ?_, ?_, ?_⟩
  · intro result
    have one := (Grading.ByteEquality.result_equal rfl 0).mp result
    exact (by decide : Grading.ByteEquality.returnValue 0 ≠ 1) one
  · exact Grading.ByteComparison.result_of_sign
      ((Grading.ByteOrder.sign_zero_iff_equal values values).mpr rfl) rfl
  · intro result
    have zero := result.zero.mpr rfl
    exact (by decide : Grading.ByteComparison.returnValue 1 ≠ 0) zero

/-- Matching only the shorter extent cannot establish exact equality or
admission under the fixed paired-count domain. -/
theorem registered_unequal_extents_rejected :
    ¬(registeredSpec .equalBytes).domain ⟨0, 0, [0x80], [0x80, 0]⟩ ∧
      ¬(registeredSpec .equalBytes).result ⟨0, 0, [0x80], [0x80, 0]⟩ 1 := by
  simp only [registeredSpec, Grading.ByteEquality.spec, Grading.ByteEquality.Result,
    Grading.ByteComparison.spec]
  decide +kernel

/-- Empty snapshots admit arbitrary bases and unused loan selectors through
the actual current-resource Pre. Only the original code/caller contract is
assumed; there is no execution or useful nonempty-domain witness here. -/
theorem registered_empty_arbitrary_base_admission (shared : OS.Borrowing.State)
    (call : OS.CallResources.Call) (original : OS.CallResources.Contract call shared)
    (leftBase rightBase flags : Word) (unused : Buffer → Nat) :
    ∃ initial, ResourcePre (registeredSpec .equalBytes) call.bytes
      ⟨shared, call, ⟨leftBase, rightBase, [], []⟩, unused⟩ initial := by
  let initial : State := {
    registers := fun register => match register with
      | .rdi => leftBase
      | .rsi => rightBase
      | .rdx => 0
      | .rsp => call.stack
      | _ => 0
    rip := call.code
    flags := flags
    memory := OS.AddressSpace.toMemory shared.resources.space }
  refine ⟨initial, ⟨⟨Grading.ByteEquality.empty_resources shared call original
    leftBase rightBase unused, rfl⟩, rfl, rfl, rfl, ?_, ?_⟩⟩
  · exact ⟨rfl, by change (0 : Nat) < 2^64; decide⟩
  · exact (Grading.ByteEquality.bound_iff _ _).mpr ⟨rfl, rfl, rfl⟩

theorem registered_empty_boolean_one (leftBase rightBase : Word) :
    (registeredSpec .equalBytes).result ⟨leftBase, rightBase, [], []⟩
      0xffffffffffff0001 ∧
      ¬(registeredSpec .equalBytes).result ⟨leftBase, rightBase, [], []⟩
        0xffffffffffff0000 := by
  constructor
  · exact Grading.ByteEquality.result_of_equal rfl (by decide)
  · intro result
    have one := (Grading.ByteEquality.result_empty leftBase rightBase _).mp result
    exact (by decide : Grading.ByteEquality.returnValue 0xffffffffffff0000 ≠ 1) one

/-- Even unrelated live authority cannot add a DATA read to empty inputs. -/
theorem registered_empty_no_data (shared : OS.Borrowing.State)
    (call : OS.CallResources.Call) (leftBase rightBase address : Word)
    (unused : Buffer → Nat) (width : Nat) :
    ¬ReadAllowed
      (⟨shared, call, ⟨leftBase, rightBase, [], []⟩, unused⟩ :
        Resources (registeredSpec .equalBytes)) ⟨.data, address, width⟩ := by
  rintro (stack | data)
  · cases stack.1
  · exact Grading.ByteEquality.empty_no_data leftBase rightBase _ data.1

/-- Registration preserves initial admission with the same original caller,
paired snapshots, exact loans, full RAM coupling and full64 ABI bindings. -/
theorem registered_original_paired_pre (bytes : List Byte)
    (resource : Resources (registeredSpec .lexicographicBytes)) (initial : State)
    (pre : ResourcePre (registeredSpec .lexicographicBytes) bytes resource initial) :
    ResourcePre (registeredSpec .equalBytes) bytes
      ⟨resource.shared, resource.call, resource.value, resource.inputLoan⟩ initial :=
  (Grading.ByteEquality.resourcePre_comparison_iff _ _ _).mpr pre

/-- Readable snapshots cannot replace the right input's original exact loan. -/
theorem registered_missing_right_loan_rejected
    (resource : Resources (registeredSpec .equalBytes)) (shared : OS.Borrowing.State)
    (nonempty : resource.value.right ≠ [])
    (missing : ¬OS.Threads.HasLoan shared resource.call.worker
      (resource.inputLoan (Grading.ByteEquality.rightBuffer resource.value))
      (Grading.ByteEquality.rightBuffer resource.value).region) :
    ¬ResourceContract resource shared := by
  intro current
  exact missing (((Grading.ByteEquality.resourceContract_iff _ _).mp current).2.2.2.2 nonempty)

#print axioms registered_equal_dirty_upper56
#print axioms registered_unequal_same_length
#print axioms registered_noncanonical_two_rejected
#print axioms registered_equality_differs_from_lexicographic
#print axioms registered_unequal_extents_rejected
#print axioms registered_empty_arbitrary_base_admission
#print axioms registered_empty_boolean_one
#print axioms registered_empty_no_data
#print axioms registered_original_paired_pre
#print axioms registered_missing_right_loan_rejected

end EDSL.Tests.GradingByteEquality

#audit_edsl
