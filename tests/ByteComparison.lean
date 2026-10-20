/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.BufferTask
import EDSL.OS.CallResources.Domain

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.ByteComparison
open X86 X86.Sequential OS OS.AddressSpace BufferCall Grading.ByteComparison

/-- Contradictory suffixes cannot override the first unsigned-byte difference.
The positive return deliberately exceeds the range of a byte subtraction. -/
theorem unsigned_first_pair_and_free_magnitude :
    spec.result ⟨0x100000001, 0x200000003, [0x80, 0], [0x7f, 0xff]⟩
      0xdeadbeef12345678 := by
  change Grading.ByteOrder.Sign _ _ _
  refine ⟨rfl, ?_, by decide, ?_⟩
  · simp [Grading.ByteOrder.UnsignedLex, List.cons_lex_cons_iff] <;> decide
  · simp [Grading.ByteOrder.UnsignedLex, List.cons_lex_cons_iff] <;> decide

/-- Swapping operands reverses the sign. A dirty upper half does not turn
low32 -1 into a positive C int32. -/
theorem swapped_operands_negative :
    spec.result ⟨0x200000003, 0x100000001, [0x7f, 0xff], [0x80, 0]⟩
      0x12345678ffffffff := by
  change Grading.ByteOrder.Sign _ _ _
  refine ⟨rfl, ?_, by decide, ?_⟩
  · simp [Grading.ByteOrder.UnsignedLex, List.cons_lex_cons_iff] <;> decide
  · simp [Grading.ByteOrder.UnsignedLex, List.cons_lex_cons_iff] <;> decide

theorem signed_byte_or_swapped_answer_rejected :
    ¬spec.result ⟨0, 0, [0x80, 0], [0x7f, 0xff]⟩ 0x12345678ffffffff := by
  intro result
  have wrong := result.negative.mp (by decide)
  have noOrder : ¬Grading.ByteOrder.UnsignedLex [0x80, 0] [0x7f, 0xff] := by
    simp [Grading.ByteOrder.UnsignedLex, List.cons_lex_cons_iff]
  exact noOrder wrong

theorem equal_requires_low32_zero :
    spec.result ⟨0, 0, [0x80, 0xff], [0x80, 0xff]⟩ 0xa55affff00000000 ∧
      ¬spec.result ⟨0, 0, [0x80, 0xff], [0x80, 0xff]⟩ 0x0000000100000001 := by
  constructor
  · exact result_of_sign
      ((Grading.ByteOrder.sign_zero_iff_equal _ _).mpr rfl) (by decide)
  · intro result
    have zero := result.zero.mpr rfl
    have nonzero : returnValue 0x0000000100000001 ≠ 0 := by decide
    exact nonzero zero

/-- Both pointers and the count use all 64 bits; only the return is low32. -/
def registers (left right count : Word) (register : Register) : Word :=
  match register with
  | .rdi => left
  | .rsi => right
  | .rdx => count
  | _ => 0

def arguments (left right count : Word) : State where
  registers := registers left right count
  rip := 0
  flags := 0
  memory := ⟨fun _ => none, fun _ => false, fun _ => false⟩

theorem full64_arguments :
    ¬Bound spec ⟨0x100000001, 0x200000003, [0x80], [0x7f]⟩ (arguments 1 0x200000003 1) ∧
      ¬Bound spec ⟨0x100000001, 0x200000003, [0x80], [0x7f]⟩
        (arguments 0x100000001 3 1) ∧
      ¬Bound spec ⟨0x100000001, 0x200000003, [0x80], [0x7f]⟩
        (arguments 0x100000001 0x200000003 0x100000001) := by
  simp only [bound_iff]
  constructor
  · intro wrong
    have different : (1 : Word) ≠ 0x100000001 := by decide
    exact different wrong.1
  · constructor
    · intro wrong
      have different : (3 : Word) ≠ 0x200000003 := by decide
      exact different wrong.2.1
    · intro wrong
      have different : (0x100000001 : Word) ≠ 1 := by decide
      exact different wrong.2.2

/-- Unequal extents are rejected by present-only admission even when their
common prefix is equal. -/
theorem unequal_extents_rejected : ¬spec.domain ⟨0, 0, [0x80], [0x80, 0]⟩ := by
  intro domain
  have lengths := domain.1
  cases lengths

/-- The production resource bridge admits both empty inputs for arbitrary
addresses, flags and loan selectors. Only original code/caller facts are used. -/
theorem empty_pre (initial : CallResources.Domain.Initial)
    (facts : CallResources.Domain.Facts initial) (left right flags : Word)
    (unused : Buffer → Nat) :
    ResourcePre spec initial.bytes
      ⟨CallResources.Domain.shared initial, CallResources.Domain.call initial,
        ⟨left, right, [], []⟩, unused⟩
      (CallResources.Domain.machine initial (registers left right 0) flags) := by
  refine ⟨⟨empty_resources _ _ (CallResources.Domain.contract facts) left right unused, rfl⟩,
    rfl, rfl, ?_, ?_, ?_⟩
  · simp [CallResources.Domain.machine, CallResources.Domain.call]
  · exact ⟨rfl, by change (0 : Nat) < 2^64; decide⟩
  · apply (bound_iff _ _).mpr
    exact ⟨rfl, rfl, rfl⟩

theorem empty_dirty_high_return (left right : Word) :
    spec.result ⟨left, right, [], []⟩ 0xffffffffffffffff ↔ False := by
  rw [result_empty]
  decide

-- Independent literal RAM: the data spans overlap at two bytes, are unaligned,
-- and lie above 4GiB. One additional readable byte follows their union.
def supplied : Space where
  cells address := match address.toNat with
    | 4096 => some ⟨0xc3, readExecute⟩
    | 65544 => some ⟨0, readOnly⟩
    | 65545 => some ⟨0x20, readOnly⟩
    | 65546 | 65547 | 65548 | 65549 | 65550 | 65551 => some ⟨0, readOnly⟩
    | 0x100000001 => some ⟨0x80, readOnly⟩
    | 0x100000002 => some ⟨0xff, readOnly⟩
    | 0x100000003 => some ⟨0x7f, readOnly⟩
    | 0x100000004 => some ⟨0x41, readOnly⟩
    | 0x100000005 => some ⟨0x5a, readOnly⟩
    | _ => none

def declared : CallResources.Domain.Initial :=
  ⟨supplied, 7, 7, 10, 4096, [0xc3], 65544, 8192⟩

theorem original_facts : CallResources.Domain.Facts declared :=
  CallResources.Domain.check_sound (by decide +kernel)

def adopted : Borrowing.State :=
  { (CallResources.Domain.shared declared) with
    resources := Ownership.install
      (CallResources.Domain.shared declared).resources supplied 7 ⟨0x100000001, 5⟩ }

theorem adopted_valid : Borrowing.WellFormed adopted :=
  Borrowing.mutate_wellFormed _ (.adopt 7 ⟨0x100000001, 5⟩) (adopted, some ⟨2, 0⟩)
    (CallResources.Domain.shared_valid original_facts) (by rfl)

def leftShared : Borrowing.State := Borrowing.installLoan adopted
  ⟨⟨2, 0⟩, 7, Threads.principal 10, ⟨0x100000001, 3⟩⟩

theorem left_valid : Borrowing.WellFormed leftShared :=
  (Borrowing.readBorrow_wellFormed _ 7 ⟨2, 0⟩ (Threads.principal 10) ⟨0x100000001, 3⟩
    (leftShared, 2) adopted_valid (by rfl)).1

def pairedShared : Borrowing.State := Borrowing.installLoan leftShared
  ⟨⟨2, 0⟩, 7, Threads.principal 10, ⟨0x100000002, 3⟩⟩

theorem paired_valid : Borrowing.WellFormed pairedShared :=
  (Borrowing.readBorrow_wellFormed _ 7 ⟨2, 0⟩ (Threads.principal 10) ⟨0x100000002, 3⟩
    (pairedShared, 3) left_valid (by rfl)).1

def input : Input := ⟨0x100000001, 0x100000002, [0x80, 0xff, 0x7f], [0xff, 0x7f, 0x41]⟩

def resource : Resources spec :=
  ⟨pairedShared, CallResources.Domain.call declared, input,
    fun buffer => if buffer.base = 0x100000001 then 2 else 3⟩

/-- Actual current snapshots and two loans admit compatible overlapping data.
The right snapshot includes a byte that is outside the left snapshot. -/
theorem admitted : ResourceContract resource pairedShared := by
  apply (resourceContract_iff _ _).mpr
  refine ⟨⟨paired_valid, ⟨_, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩,
    original_facts.code, original_facts.stack, original_facts.returnCanonical,
    original_facts.stackBound, original_facts.postStackCanonical⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    intro offset byte present
    match offset with
    | 0 | 1 | 2 => simp [resource, input] at present; subst byte; rfl
    | offset + 3 => simp [resource, input] at present
  · refine ⟨by decide, ?_⟩
    intro offset byte present
    match offset with
    | 0 | 1 | 2 => simp [resource, input] at present; subst byte; rfl
    | offset + 3 => simp [resource, input] at present
  · intro _
    exact ⟨_, rfl, rfl, rfl⟩
  · intro _
    exact ⟨_, rfl, rfl, rfl⟩

theorem paired_pre : ResourcePre spec declared.bytes resource
    (CallResources.Domain.machine declared
      (registers 0x100000001 0x100000002 3) 0) := by
  refine ⟨⟨admitted, rfl⟩, rfl, rfl, rfl, ⟨rfl, by decide⟩, ?_⟩
  exact (bound_iff _ _).mpr ⟨rfl, rfl, rfl⟩

/-- Both actual DATA1 operands derive authority from the production policy,
including the final right byte that the left loan cannot cover. -/
theorem two_buffer_reads :
    ReadAllowed resource ⟨.data, 0x100000001, 1⟩ ∧
      ReadAllowed resource ⟨.data, 0x100000004, 1⟩ ∧
      readDataByte (toMemory pairedShared.resources.space) 0x100000001 = .ok 0x80 ∧
      readDataByte (toMemory pairedShared.resources.space) 0x100000004 = .ok 0x41 := by
  have left : DataRead (spec.buffers resource.value) ⟨.data, 0x100000001, 1⟩ :=
    dataRead_left (by unfold Buffer.Contains leftBuffer; decide)
  have right : DataRead (spec.buffers resource.value) ⟨.data, 0x100000004, 1⟩ :=
    dataRead_right (by unfold Buffer.Contains rightBuffer; decide)
  exact ⟨.inr ⟨left, admitted.dataRead_permission left⟩,
    .inr ⟨right, admitted.dataRead_permission right⟩, rfl, rfl⟩

/-- Readability and the other input's loan cannot replace a missing right ID. -/
theorem missing_right_denied :
    ¬ResourceContract {resource with inputLoan :=
      fun buffer => if buffer.base = 0x100000001 then 2 else 99} pairedShared := by
  intro contract
  obtain ⟨loan, live, _, _⟩ := contract.inputs (rightBuffer input)
    (by simp [spec, resource]) (by decide)
  change none = some loan at live
  cases live

def shortShared : Borrowing.State := Borrowing.installLoan leftShared
  ⟨⟨2, 0⟩, 7, Threads.principal 10, ⟨0x100000002, 2⟩⟩

/-- The real borrowing API accepts the shorter read-only loan, but the fixed
comparison contract requires the complete right snapshot's exact extent. -/
theorem short_right_denied :
    Borrowing.readBorrow leftShared 7 ⟨2, 0⟩ (Threads.principal 10) ⟨0x100000002, 2⟩ =
      .ok (shortShared, 3) ∧ ¬ResourceContract resource shortShared := by
  refine ⟨rfl, ?_⟩
  intro contract
  obtain ⟨loan, live, _, region⟩ := contract.inputs (rightBuffer input)
    (by simp [spec, resource]) (by decide)
  have exactLoan : loan = ⟨⟨2, 0⟩, 7, Threads.principal 10, ⟨0x100000002, 2⟩⟩ :=
    (Option.some.inj live).symm
  subst loan
  have different : (⟨0x100000002, 2⟩ : Region) ≠ (rightBuffer input).region := by decide
  exact different region

def revoked : Borrowing.State :=
  { pairedShared with loans := fun identifier =>
      if identifier = 3 then none else pairedShared.loans identifier }

/-- Real revocation preserves RAM and snapshots while invalidating current
right-buffer authority. A past snapshot cannot revive the required loan. -/
theorem revoked_right_denied :
    Borrowing.finishLoan pairedShared (Threads.principal 10) 3 = .ok revoked ∧
      toMemory revoked.resources.space = toMemory pairedShared.resources.space ∧
      ¬ResourceContract resource revoked := by
  refine ⟨rfl, rfl, ?_⟩
  intro contract
  obtain ⟨loan, live, _, _⟩ := contract.inputs (rightBuffer input)
    (by simp [spec, resource]) (by decide)
  change none = some loan at live
  cases live

def extraShared : Borrowing.State := Borrowing.installLoan pairedShared
  ⟨⟨2, 0⟩, 7, Threads.principal 10, ⟨0x100000001, 5⟩⟩

/-- An unrelated wider loan really authorizes a readable DATA4 load. It still
cannot widen either fixed byte snapshot or admit a readable neighbor. -/
theorem foreign_loan_cannot_widen :
    Borrowing.readBorrow pairedShared 7 ⟨2, 0⟩ (Threads.principal 10) ⟨0x100000001, 5⟩ =
        .ok (extraShared, 4) ∧
      Borrowing.loadWord extraShared (Threads.principal 10) 4 0x100000002 = .ok 0x5a417fff ∧
      ¬ReadAllowed {resource with shared := extraShared} ⟨.data, 0x100000002, 4⟩ ∧
      ¬ReadAllowed {resource with shared := extraShared} ⟨.data, 0x100000005, 1⟩ := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro allowed
    rcases allowed with stack | data
    · cases stack.1
    · have spans := (dataRead_iff _ _).mp data.1
      have outside : ¬((leftBuffer input).Contains 0x100000002 4 ∨
          (rightBuffer input).Contains 0x100000002 4) := by
        unfold Buffer.Contains leftBuffer rightBuffer input
        decide
      exact outside spans.2
  · intro allowed
    rcases allowed with stack | data
    · cases stack.1
    · have spans := (dataRead_iff _ _).mp data.1
      have outside : ¬((leftBuffer input).Contains 0x100000005 1 ∨
          (rightBuffer input).Contains 0x100000005 1) := by
        unfold Buffer.Contains leftBuffer rightBuffer input
        decide
      exact outside spans.2

/-- Compatible identical code aliases reuse original code authority; the
fixed task imposes no data/code disjointness or distinct-loan requirement. -/
theorem code_alias_admitted (call : CallResources.Call) (shared : Borrowing.State)
    (original : CallResources.Contract call shared) :
    ResourceContract (⟨shared, call, ⟨call.code, call.code, call.bytes, call.bytes⟩,
      fun _ => call.codeLoan⟩ : Resources spec) shared := by
  apply (resourceContract_iff _ _).mpr
  exact ⟨original, original.code.readable, original.code.readable,
    fun _ => original.codeLoan, fun _ => original.codeLoan⟩

def callerResource : Resources spec :=
  ⟨CallResources.Domain.shared declared, CallResources.Domain.call declared,
    ⟨65544, 65544, [0, 0x20, 0, 0, 0, 0, 0, 0], [0, 0x20, 0, 0, 0, 0, 0, 0]⟩,
    fun _ => 1⟩

/-- The original caller slot may also serve as both data snapshots. Reading
its final byte as DATA1 retains the exact original caller loan. -/
theorem caller_alias_data :
    ResourceContract callerResource callerResource.shared ∧
      ReadAllowed callerResource ⟨.data, 65551, 1⟩ := by
  have snapshot : BufferAt (toMemory callerResource.shared.resources.space)
      65544 [0, 0x20, 0, 0, 0, 0, 0, 0] := by
    refine ⟨by decide, ?_⟩
    intro offset byte present
    match offset with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => simp at present; subst byte; rfl
    | offset + 8 => simp at present
  have contract : ResourceContract callerResource callerResource.shared := by
    apply (resourceContract_iff _ _).mpr
    exact ⟨CallResources.Domain.contract original_facts, snapshot, snapshot,
      fun _ => CallResources.Domain.stack_held declared,
      fun _ => CallResources.Domain.stack_held declared⟩
  have footprint : DataRead (spec.buffers callerResource.value) ⟨.data, 65551, 1⟩ :=
    dataRead_right (by unfold Buffer.Contains rightBuffer; decide)
  exact ⟨contract, .inr ⟨footprint, contract.dataRead_permission footprint⟩⟩

end EDSL.Tests.ByteComparison
