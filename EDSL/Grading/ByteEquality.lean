/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.ByteComparison

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Grading.ByteEquality
open X86 X86.Sequential BufferCall

abbrev Input := ByteComparison.Input
abbrev leftBuffer := ByteComparison.leftBuffer
abbrev rightBuffer := ByteComparison.rightBuffer

/-- The C Boolean ABI observes only low8 RAX. The other 56 bits are free. -/
def returnValue (actual : Word) : Byte := actual.setWidth 8

/-- Complete mathematical list equality, with canonical Boolean results.
In particular, a nonzero byte other than one is not a successful result. -/
def Result (input : Input) (actual : Word) : Prop :=
  returnValue actual = if input.left = input.right then 1 else 0

/-- Reuse the full-width paired-buffer admission contract, current loans,
compatible overlaps, and empty-input policy. Only the return relation changes.
Stable ordinary RAM, modeled authority and absent asynchronous interference
remain environmental assumptions of the sequential callable profile. -/
def spec : BufferCall.Spec := { ByteComparison.spec with result := Result }

theorem domain_iff (input : Input) :
    spec.domain input ↔ input.left.length = input.right.length ∧ input.left.length < 2^64 :=
  ByteComparison.domain_iff input

theorem bound_iff (input : Input) (initial : State) :
    Bound spec input initial ↔
      initial.registers .rdi = input.leftBase ∧
      initial.registers .rsi = input.rightBase ∧
      initial.registers .rdx = BitVec.ofNat 64 input.left.length :=
  ByteComparison.bound_iff input initial

theorem snapshots_iff (input : Input) (memory : Memory) :
    (∀ buffer ∈ spec.buffers input, BufferAt memory buffer.base buffer.bytes) ↔
      BufferAt memory input.leftBase input.left ∧
      BufferAt memory input.rightBase input.right :=
  ByteComparison.snapshots_iff input memory

/-- This view changes no snapshot, current loan, worker or original call. -/
def comparisonResources (resource : Resources spec) : Resources ByteComparison.spec :=
  ⟨resource.shared, resource.call, resource.value, resource.inputLoan⟩

theorem resourceContract_comparison_iff (resource : Resources spec)
    (shared : OS.Borrowing.State) :
    ResourceContract resource shared ↔
      ResourceContract (comparisonResources resource) shared := by
  constructor <;> intro contract
  · exact ⟨contract.call, contract.buffers, contract.inputs⟩
  · exact ⟨contract.call, contract.buffers, contract.inputs⟩

theorem resourcePre_comparison_iff (bytes : List Byte) (resource : Resources spec)
    (initial : State) :
    ResourcePre spec bytes resource initial ↔
      ResourcePre ByteComparison.spec bytes (comparisonResources resource) initial := by
  constructor <;> intro pre
  · exact ⟨⟨(resourceContract_comparison_iff _ _).mp pre.current.contract,
      pre.current.coupled⟩, pre.code, pre.entry,
      pre.stack, pre.domain, pre.arguments⟩
  · exact ⟨⟨(resourceContract_comparison_iff _ _).mpr pre.current.contract,
      pre.current.coupled⟩, pre.code, pre.entry,
      pre.stack, pre.domain, pre.arguments⟩

/-- Both original exact input loans are retained, even for overlapping spans. -/
theorem resourceContract_iff (resource : Resources spec) (shared : OS.Borrowing.State) :
    ResourceContract resource shared ↔
      OS.CallResources.Contract resource.call shared ∧
      BufferAt (OS.AddressSpace.toMemory shared.resources.space)
        resource.value.leftBase resource.value.left ∧
      BufferAt (OS.AddressSpace.toMemory shared.resources.space)
        resource.value.rightBase resource.value.right ∧
      (resource.value.left ≠ [] → OS.Threads.HasLoan shared resource.call.worker
        (resource.inputLoan (leftBuffer resource.value)) (leftBuffer resource.value).region) ∧
      (resource.value.right ≠ [] → OS.Threads.HasLoan shared resource.call.worker
        (resource.inputLoan (rightBuffer resource.value)) (rightBuffer resource.value).region) :=
  (resourceContract_comparison_iff resource shared).trans
    (ByteComparison.resourceContract_iff (comparisonResources resource) shared)

theorem dataRead_iff (input : Input) (read : Read) :
    DataRead (spec.buffers input) read ↔ read.kind = .data ∧
      ((leftBuffer input).Contains read.address read.bytes ∨
        (rightBuffer input).Contains read.address read.bytes) :=
  ByteComparison.dataRead_iff input read

theorem readAllowed_comparison_iff (resource : Resources spec) (read : Read) :
    ReadAllowed resource read ↔ ReadAllowed (comparisonResources resource) read := Iff.rfl

theorem empty_resources (shared : OS.Borrowing.State) (call : OS.CallResources.Call)
    (original : OS.CallResources.Contract call shared) (leftBase rightBase : Word)
    (unused : Buffer → Nat) :
    ResourceContract (⟨shared, call, ⟨leftBase, rightBase, [], []⟩, unused⟩ : Resources spec)
      shared :=
  (resourceContract_comparison_iff _ _).mpr
    (ByteComparison.empty_resources shared call original leftBase rightBase unused)

theorem empty_no_data (leftBase rightBase : Word) (read : Read) :
    ¬DataRead (spec.buffers ⟨leftBase, rightBase, [], []⟩) read :=
  ByteComparison.empty_no_data leftBase rightBase read

theorem result_iff (input : Input) (actual : Word) :
    spec.result input actual ↔
      returnValue actual = if input.left = input.right then 1 else 0 := Iff.rfl

theorem result_of_low8_eq {input : Input} {a b : Word}
    (same : a.setWidth 8 = b.setWidth 8) :
    spec.result input a ↔ spec.result input b := by
  change returnValue a = _ ↔ returnValue b = _
  rw [returnValue, returnValue, same]

theorem result_equal {input : Input} (same : input.left = input.right) (actual : Word) :
    spec.result input actual ↔ returnValue actual = 1 := by
  simp only [result_iff, same, ↓reduceIte]

theorem result_mismatch {input : Input} (different : input.left ≠ input.right) (actual : Word) :
    spec.result input actual ↔ returnValue actual = 0 := by
  simp only [result_iff, different, ↓reduceIte]

theorem result_cases (input : Input) (actual : Word) :
    spec.result input actual ↔
      (input.left = input.right ∧ returnValue actual = 1) ∨
      (input.left ≠ input.right ∧ returnValue actual = 0) := by
  by_cases same : input.left = input.right <;> simp [result_iff, same]

theorem result_low8_one_iff_equal {input : Input} {actual : Word}
    (result : spec.result input actual) :
    returnValue actual = 1 ↔ input.left = input.right := by
  rcases (result_cases _ _).mp result with ⟨same, returned⟩ | ⟨different, returned⟩
  · simp [same, returned]
  · simp [different, returned]

theorem result_low8_zero_iff_unequal {input : Input} {actual : Word}
    (result : spec.result input actual) :
    returnValue actual = 0 ↔ input.left ≠ input.right := by
  rcases (result_cases _ _).mp result with ⟨same, returned⟩ | ⟨different, returned⟩
  · simp [same, returned]
  · simp [different, returned]

theorem result_rejects_noncanonical {input : Input} {actual : Word}
    (notZero : returnValue actual ≠ 0) (notOne : returnValue actual ≠ 1) :
    ¬spec.result input actual := by
  intro result
  rcases (result_cases _ _).mp result with ⟨_, returned⟩ | ⟨_, returned⟩
  · exact notOne returned
  · exact notZero returned

theorem result_of_equal {input : Input} {actual : Word}
    (same : input.left = input.right) (returned : returnValue actual = 1) :
    spec.result input actual := (result_equal same actual).mpr returned

theorem result_of_mismatch {input : Input} {actual : Word}
    (different : input.left ≠ input.right) (returned : returnValue actual = 0) :
    spec.result input actual := (result_mismatch different actual).mpr returned

/-- Any actual unequal byte refutes complete equality, regardless of suffixes. -/
theorem unequal_at {left right : List Byte} {index : Nat} {a b : Byte}
    (leftAt : left[index]? = some a) (rightAt : right[index]? = some b)
    (different : a ≠ b) : left ≠ right := by
  intro same
  rw [same] at leftAt
  exact different (Option.some.inj (leftAt.symm.trans rightAt))

theorem result_at_mismatch {input : Input} {index : Nat} {a b : Byte} {actual : Word}
    (leftAt : input.left[index]? = some a) (rightAt : input.right[index]? = some b)
    (different : a ≠ b) (returned : returnValue actual = 0) :
    spec.result input actual :=
  result_of_mismatch (unequal_at leftAt rightAt different) returned

/-- A generated first-mismatch search can discharge the Boolean contract
without relating a return to subtraction or lexicographic signs. -/
theorem result_at_first_unequal {input : Input} {index : Nat} {actual : Word}
    (sameLength : input.left.length = input.right.length)
    (first : FirstMatch.Result (input.left.zip input.right)
      (fun pair => pair.1 != pair.2) index)
    (inside : index < input.left.length) (returned : returnValue actual = 0) :
    spec.result input actual := by
  obtain ⟨_, _, _, leftAt, rightAt, different⟩ :=
    ByteOrder.result_first_unequal sameLength first inside
  exact result_at_mismatch leftAt rightAt different returned

/-- Exhaustion is sound only with the complete paired extent. -/
theorem result_of_exhaustion {input : Input} {actual : Word}
    (sameLength : input.left.length = input.right.length)
    (exhausted : FirstMatch.Result (input.left.zip input.right)
      (fun pair => pair.1 != pair.2) input.left.length)
    (returned : returnValue actual = 1) : spec.result input actual :=
  result_of_equal ((FirstMatch.Consumers.paired_exhaustion_iff_equal sameLength).mp exhausted)
    returned

theorem result_of_prefix_exhaustion {input : Input} {index : Nat} {actual : Word}
    (sameLength : input.left.length = input.right.length)
    (scanned : FirstMatch.Prefix (input.left.zip input.right)
      (fun pair => pair.1 != pair.2) index)
    (finished : index = input.left.length) (returned : returnValue actual = 1) :
    spec.result input actual := by
  apply result_of_equal _ returned
  calc
    input.left = input.left.take index := by rw [finished, List.take_length]
    _ = input.right.take index := ByteOrder.paired_prefix_equal scanned
    _ = input.right := by rw [finished.trans sameLength, List.take_length]

/-- Existence is independent of machine execution and even of domain admission. -/
theorem result_exists (input : Input) : ∃ actual : Word, spec.result input actual := by
  by_cases same : input.left = input.right
  · exact ⟨1, result_of_equal same rfl⟩
  · exact ⟨0, result_of_mismatch same rfl⟩

theorem result_empty (leftBase rightBase actual : Word) :
    spec.result ⟨leftBase, rightBase, [], []⟩ actual ↔ returnValue actual = 1 :=
  result_equal rfl actual

end EDSL.Grading.ByteEquality
