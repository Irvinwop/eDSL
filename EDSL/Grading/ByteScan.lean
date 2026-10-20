/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.BufferCall.Resources

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Grading.ByteScan
open X86

/-- Independent bounded NUL length: at most n, all earlier bytes nonzero,
and a zero byte at the result whenever it is smaller than n. No code shape,
fuel, decoder, resource checker or future machine result defines this relation. -/
structure BoundedNulLength (values : List Byte) (result : Nat) : Prop where
  bound : result ≤ values.length
  nonzero : ∀ index, index < result → values[index]? ≠ some 0
  zero : result < values.length → values[result]? = some 0

/-- Two results meeting the mathematical contract must be equal, including
inputs with multiple NULs. A later match cannot satisfy the prefix condition. -/
theorem BoundedNulLength.unique {values : List Byte} {a b : Nat}
    (first : BoundedNulLength values a) (second : BoundedNulLength values b) : a = b := by
  by_cases same : a = b
  · exact same
  · have bounds := first.bound
    have otherBound := second.bound
    rcases Nat.lt_or_gt_of_ne same with earlier | later
    · exact False.elim (second.nonzero a earlier (first.zero (by omega)))
    · exact False.elim (first.nonzero b later (second.zero (by omega)))

/-- The relation is total on finite byte lists, without any artificial small
count or execution-fuel bound. This is a mathematical existence proof only. -/
theorem BoundedNulLength.exists (values : List Byte) : ∃ result, BoundedNulLength values result := by
  induction values with
  | nil => exact ⟨0, by constructor <;> simp⟩
  | cons byte tail induction =>
    by_cases isZero : byte = 0
    · exact ⟨0, by constructor <;> simp [isZero]⟩
    · obtain ⟨result, contract⟩ := induction
      refine ⟨result + 1, ⟨by simpa using Nat.succ_le_succ contract.bound, ?_, ?_⟩⟩
      · intro index before
        cases index with
        | zero => simpa using isZero
        | succ index =>
          simpa using contract.nonzero index (by omega)
      · intro inside
        have bound : result < tail.length := by simpa using inside
        simpa using contract.zero bound

theorem BoundedNulLength.nil_iff (result : Nat) : BoundedNulLength [] result ↔ result = 0 := by
  constructor
  · intro contract
    have bound := contract.bound
    simpa using bound
  · rintro rfl
    constructor <;> simp

theorem BoundedNulLength.of_nonzero (values : List Byte)
    (nonzero : ∀ index, index < values.length → values[index]? ≠ some 0) :
    BoundedNulLength values values.length :=
  ⟨Nat.le_refl _, nonzero, by omega⟩

/-- A reusable scan-prefix invariant, independent of registers or instructions. -/
def NonzeroPrefix (values : List Byte) (count : Nat) : Prop :=
  count ≤ values.length ∧ ∀ index, index < count → values[index]? ≠ some 0

theorem NonzeroPrefix.start (values : List Byte) : NonzeroPrefix values 0 := by
  exact ⟨Nat.zero_le _, by omega⟩

theorem NonzeroPrefix.advance {values : List Byte} {count : Nat} {byte : Byte}
    (scanned : NonzeroPrefix values count) (present : values[count]? = some byte)
    (nonzero : byte ≠ 0) : NonzeroPrefix values (count + 1) := by
  obtain ⟨inside, _⟩ := List.getElem_of_getElem? present
  refine ⟨by omega, ?_⟩
  intro index before
  by_cases earlier : index < count
  · exact scanned.2 index earlier
  · have same : index = count := by omega
    rw [same, present]
    simpa using nonzero

theorem NonzeroPrefix.finish_zero {values : List Byte} {count : Nat}
    (scanned : NonzeroPrefix values count) (zero : values[count]? = some 0) :
    BoundedNulLength values count := ⟨scanned.1, scanned.2, fun _ => zero⟩

theorem NonzeroPrefix.finish_bound {values : List Byte} {count : Nat}
    (scanned : NonzeroPrefix values count) (done : count = values.length) :
    BoundedNulLength values count := ⟨scanned.1, scanned.2, by omega⟩

/-- Exactly n initial bytes, where n is values.length. The pointer is an actual
64-bit value; the empty input admits null, one-past and noncanonical pointers. -/
structure Input where
  base : Word
  values : List Byte

/-- Independent strnlen-style contract. RDI is the base, RSI is n; all remaining
arguments are unrestricted. The mathematical count is below 2^64 and BufferAt
adds the natural nonwrapping resource span. No registration is performed here. -/
def spec : BufferCall.Spec where
  Input := Input
  arguments input index :=
    match index.val with
    | 0 => some (.word64 input.base)
    | 1 => some (.word64 (BitVec.ofNat 64 input.values.length))
    | _ => none
  buffers input := [⟨input.base, input.values⟩]
  domain input := input.values.length < 2^64
  result input actual := BoundedNulLength input.values actual.toNat
  useful input := input.values ≠ []

/-- Every admitted mathematical list has one full-width machine result. -/
theorem result_exists {input : Input} (domain : spec.domain input) :
    ∃ result : Word, spec.result input result := by
  obtain ⟨result, contract⟩ := BoundedNulLength.exists input.values
  have small : result < 2^64 := by
    change input.values.length < 2^64 at domain
    have bound := contract.bound
    omega
  refine ⟨BitVec.ofNat 64 result, ?_⟩
  change BoundedNulLength input.values (BitVec.ofNat 64 result).toNat
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] using contract

theorem result_unique {input : Input} {a b : Word}
    (first : spec.result input a) (second : spec.result input b) : a = b :=
  BitVec.eq_of_toNat_eq (BoundedNulLength.unique first second)

/-- Empty input's exact full-width return is zero, for every pointer. -/
theorem result_empty (base : Word) (result : Word) :
    spec.result ⟨base, []⟩ result ↔ result = 0 := by
  change BoundedNulLength [] result.toNat ↔ result = 0
  rw [BoundedNulLength.nil_iff]
  constructor
  · intro zero
    exact BitVec.eq_of_toNat_eq zero
  · rintro rfl
    rfl

end EDSL.Grading.ByteScan
