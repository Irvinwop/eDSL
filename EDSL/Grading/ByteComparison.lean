/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.ByteOrder
import EDSL.BufferCall.Resources

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Grading.ByteComparison
open X86 X86.Sequential BufferCall

/-- Independent snapshots at two full-width addresses. The common count is
the left length; equal lengths belong to the mathematical domain. -/
structure Input where
  leftBase : Word
  rightBase : Word
  left : List Byte
  right : List Byte

def leftBuffer (input : Input) : Buffer := ⟨input.leftBase, input.left⟩
def rightBuffer (input : Input) : Buffer := ⟨input.rightBase, input.right⟩

/-- The C int32 return ABI observes signed low32 RAX. Upper RAX bits and the
magnitude of a nonzero result are unrestricted. -/
def returnValue (actual : Word) : Int := (actual.setWidth 32).toInt

/-- Fixed unsigned-byte lexicographic comparison, independent of code shape,
first-match search, subtraction, execution and resource checking. -/
def Result (input : Input) (actual : Word) : Prop :=
  ByteOrder.Sign input.left input.right (returnValue actual)

/-- RDI/RSI/RDX are the complete left pointer/right pointer/count. Nonempty
snapshots require complete readable, nonwrapping spans and exact current loans
through BufferCall; compatible unaligned read-only aliases are admitted,
including aliases with original code/caller bytes. Empty snapshots need no
data read, loan, alignment, allocation or pointer validity on either side.

Stable ordinary RAM, modeled authority and absent asynchronous interference
remain the sequential callable profile's environmental assumptions. -/
def spec : BufferCall.Spec where
  Input := Input
  arguments input index :=
    match index.val with
    | 0 => some (.word64 input.leftBase)
    | 1 => some (.word64 input.rightBase)
    | 2 => some (.word64 (BitVec.ofNat 64 input.left.length))
    | _ => none
  buffers input := [leftBuffer input, rightBuffer input]
  domain input := input.left.length = input.right.length ∧ input.left.length < 2^64
  result := Result
  useful input := input.left ≠ []

theorem domain_iff (input : Input) :
    spec.domain input ↔ input.left.length = input.right.length ∧ input.left.length < 2^64 :=
  Iff.rfl

/-- A shared paired VCG can recover all three full-width ABI bindings. -/
theorem bound_iff (input : Input) (initial : State) :
    Bound spec input initial ↔
      initial.registers .rdi = input.leftBase ∧
      initial.registers .rsi = input.rightBase ∧
      initial.registers .rdx = BitVec.ofNat 64 input.left.length := by
  constructor
  · intro bound
    have left := bound (0 : Fin 6) (.word64 input.leftBase) rfl
    have right := bound (1 : Fin 6) (.word64 input.rightBase) rfl
    have count := bound (2 : Fin 6) (.word64 (BitVec.ofNat 64 input.left.length)) rfl
    exact ⟨left, right, count⟩
  · rintro ⟨left, right, count⟩ index argument binding
    obtain ⟨index, inside⟩ := index
    match index with
    | 0 => simp [spec] at binding; subst argument; exact left
    | 1 => simp [spec] at binding; subst argument; exact right
    | 2 => simp [spec] at binding; subst argument; exact count
    | index + 3 => simp [spec] at binding

theorem snapshots_iff (input : Input) (memory : Memory) :
    (∀ buffer ∈ spec.buffers input, BufferAt memory buffer.base buffer.bytes) ↔
      BufferAt memory input.leftBase input.left ∧
      BufferAt memory input.rightBase input.right := by
  simp [spec, leftBuffer, rightBuffer]

/-- Each nonempty side needs its exact current loan, even if the other side
is already readable. Identical compatible descriptors may share a loan ID. -/
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
        (resource.inputLoan (rightBuffer resource.value)) (rightBuffer resource.value).region) := by
  constructor
  · intro contract
    obtain ⟨left, right⟩ := (snapshots_iff _ _).mp contract.buffers
    exact ⟨contract.call, left, right,
      contract.inputs (leftBuffer resource.value) (by simp [spec]),
      contract.inputs (rightBuffer resource.value) (by simp [spec])⟩
  · rintro ⟨call, left, right, leftLoan, rightLoan⟩
    refine ⟨call, (snapshots_iff _ _).mpr ⟨left, right⟩, ?_⟩
    intro buffer member nonempty
    have cases : buffer = leftBuffer resource.value ∨ buffer = rightBuffer resource.value := by
      simpa [spec] using member
    rcases cases with rfl | rfl
    · exact leftLoan nonempty
    · exact rightLoan nonempty

/-- A positive DATA operand fits one complete initial snapshot. Neighboring
readable RAM and unrelated loans cannot enlarge either admitted span. -/
theorem dataRead_iff (input : Input) (read : Read) :
    DataRead (spec.buffers input) read ↔ read.kind = .data ∧
      ((leftBuffer input).Contains read.address read.bytes ∨
        (rightBuffer input).Contains read.address read.bytes) := by
  simp [DataRead, spec]

theorem dataRead_left {input : Input} {address : Word} {width : Nat}
    (span : (leftBuffer input).Contains address width) :
    DataRead (spec.buffers input) ⟨.data, address, width⟩ :=
  (dataRead_iff _ _).mpr ⟨rfl, Or.inl span⟩

theorem dataRead_right {input : Input} {address : Word} {width : Nat}
    (span : (rightBuffer input).Contains address width) :
    DataRead (spec.buffers input) ⟨.data, address, width⟩ :=
  (dataRead_iff _ _).mpr ⟨rfl, Or.inr span⟩

/-- Original code/caller authority suffices for both empty buffers, for every
pair of bases and every input-loan selector, including absent identifiers. -/
theorem empty_resources (shared : OS.Borrowing.State) (call : OS.CallResources.Call)
    (original : OS.CallResources.Contract call shared) (leftBase rightBase : Word)
    (unused : Buffer → Nat) :
    ResourceContract (⟨shared, call, ⟨leftBase, rightBase, [], []⟩, unused⟩ : Resources spec)
      shared := by
  apply ResourceContract.of_empty original
  intro buffer member
  have cases : buffer = leftBuffer ⟨leftBase, rightBase, [], []⟩ ∨
      buffer = rightBuffer ⟨leftBase, rightBase, [], []⟩ := by
    simpa [spec] using member
  rcases cases with rfl | rfl <;> rfl

theorem empty_no_data (leftBase rightBase : Word) (read : Read) :
    ¬DataRead (spec.buffers ⟨leftBase, rightBase, [], []⟩) read := by
  apply DataRead.no_empty
  intro buffer member
  have cases : buffer = leftBuffer ⟨leftBase, rightBase, [], []⟩ ∨
      buffer = rightBuffer ⟨leftBase, rightBase, [], []⟩ := by
    simpa [spec] using member
  rcases cases with rfl | rfl <;> rfl

theorem result_iff (input : Input) (actual : Word) :
    spec.result input actual ↔ ByteOrder.Sign input.left input.right (returnValue actual) :=
  Iff.rfl

theorem returnValue_zeroExtend (actual : BitVec 32) :
    returnValue (actual.zeroExtend 64) = actual.toInt := by
  simp [returnValue]

theorem returnValue_zero_iff (actual : Word) :
    returnValue actual = 0 ↔ actual.setWidth 32 = 0 := by
  change (actual.setWidth 32).toInt = (0 : BitVec 32).toInt ↔ _
  exact BitVec.toInt_inj

theorem result_of_low32_eq {input : Input} {a b : Word}
    (same : a.setWidth 32 = b.setWidth 32) :
    spec.result input a ↔ spec.result input b := by
  change ByteOrder.Sign _ _ (returnValue a) ↔ ByteOrder.Sign _ _ (returnValue b)
  rw [returnValue, returnValue, same]

theorem result_zero_iff_equal {input : Input} {actual : Word}
    (result : spec.result input actual) :
    returnValue actual = 0 ↔ input.left = input.right := result.zero

theorem result_low32_zero_iff_equal {input : Input} {actual : Word}
    (result : spec.result input actual) :
    actual.setWidth 32 = 0 ↔ input.left = input.right :=
  (returnValue_zero_iff actual).symm.trans result.zero

/-- The fixed C return can be proved from any signed low32 value meeting the
independent sign relation; no exact subtraction magnitude is required. -/
theorem result_of_sign {input : Input} {actual : Word} {value : Int}
    (sign : ByteOrder.Sign input.left input.right value)
    (returned : returnValue actual = value) : spec.result input actual := by
  change ByteOrder.Sign _ _ (returnValue actual)
  rw [returned]
  exact sign

theorem result_at_first_unequal {input : Input} {index : Nat} {a b : Byte} {actual : Word}
    (sameLength : input.left.length = input.right.length)
    (prefixEqual : input.left.take index = input.right.take index)
    (leftAt : input.left[index]? = some a) (rightAt : input.right[index]? = some b)
    (different : a ≠ b) (returned : returnValue actual = ByteOrder.signedDifference a b) :
    spec.result input actual :=
  result_of_sign (ByteOrder.sign_at_first_unequal sameLength prefixEqual leftAt rightAt different)
    returned

theorem result_of_exhaustion {input : Input} {actual : Word}
    (sameLength : input.left.length = input.right.length)
    (exhausted : FirstMatch.Result (input.left.zip input.right)
      (fun pair => pair.1 != pair.2) input.left.length)
    (returned : returnValue actual = 0) : spec.result input actual :=
  result_of_sign ((ByteOrder.result_exhaustion_iff_sign_zero sameLength).mp exhausted) returned

/-- Every domain input admits a machine return. The unrestricted mathematical
count is independent of execution bounds; a byte difference fits C int32. -/
theorem result_exists {input : Input} (domain : spec.domain input) :
    ∃ actual : Word, spec.result input actual := by
  obtain ⟨index, first⟩ := FirstMatch.Result.exists (input.left.zip input.right)
    (fun pair => pair.1 != pair.2)
  rcases ByteOrder.result_sign_cases domain.1 first with exhausted | found
  · exact ⟨0, result_of_sign exhausted.2 rfl⟩
  · obtain ⟨a, b, _, _, _, sign, _⟩ := found.2
    exact ⟨(a.zeroExtend 32 - b.zeroExtend 32).zeroExtend 64,
      result_of_sign sign (returnValue_zeroExtend _)⟩

/-- Empty comparison returns low32 zero for arbitrary pointers and upper RAX. -/
theorem result_empty (leftBase rightBase actual : Word) :
    spec.result ⟨leftBase, rightBase, [], []⟩ actual ↔ returnValue actual = 0 := by
  constructor
  · intro result
    exact result.zero.mpr rfl
  · intro returned
    exact result_of_sign ((ByteOrder.sign_zero_iff_equal [] []).mpr rfl) returned

end EDSL.Grading.ByteComparison
