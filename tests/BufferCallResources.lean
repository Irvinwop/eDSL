/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.ByteScan
import EDSL.OS.CallResources.Domain

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.BufferCallResources
open X86 OS OS.AddressSpace BufferCall
abbrev Scan := Grading.ByteScan.Input

/-- Only the two original code/caller loans exist. Every base and unused loan
ID, including absent IDs, is admitted for n=0 in the actual resource precondition. -/
def emptyResources (initial : CallResources.Domain.Initial) (base : Word) (unused : Nat) :
    Resources Grading.ByteScan.spec :=
  ⟨CallResources.Domain.shared initial, CallResources.Domain.call initial,
    ⟨base, []⟩, fun _ => unused⟩

def emptyMachine (initial : CallResources.Domain.Initial) (base flags : Word) : State :=
  CallResources.Domain.machine initial (fun register => if register = .rdi then base else 0) flags

theorem empty_pre (initial : CallResources.Domain.Initial)
    (facts : CallResources.Domain.Facts initial) (base : Word) (unused : Nat) (flags : Word) :
    ResourcePre Grading.ByteScan.spec initial.bytes (emptyResources initial base unused)
      (emptyMachine initial base flags) := by
  refine ⟨⟨ResourceContract.of_empty (CallResources.Domain.contract facts) ?_, rfl⟩,
    rfl, rfl, ?_, by change (0 : Nat) < 2^64; decide, ?_⟩
  · intro buffer member
    have same : buffer = ⟨base, []⟩ := by
      simpa [emptyResources, Grading.ByteScan.spec] using member
    rw [same]
  · simp [emptyMachine, CallResources.Domain.machine, emptyResources, CallResources.Domain.call]
  · intro index argument binding
    obtain ⟨index, bound⟩ := index
    match index with
    | 0 =>
      simp [emptyResources, Grading.ByteScan.spec] at binding
      subst argument
      rfl
    | 1 =>
      simp [emptyResources, Grading.ByteScan.spec] at binding
      subst argument
      rfl
    | index + 2 => simp [emptyResources, Grading.ByteScan.spec] at binding

-- An unaligned input above 4GiB has a readable byte beyond its exact eight-byte
-- loan. Literal current bytes, not the qword writer, fix the byte order.
def supplied : Space where
  cells address := match address.toNat with
    | 4096 => some ⟨0xc3, readExecute⟩
    | 65544 => some ⟨0, readOnly⟩
    | 65545 => some ⟨0x20, readOnly⟩
    | 65546 | 65547 | 65548 | 65549 | 65550 | 65551 => some ⟨0, readOnly⟩
    | 0x100000001 => some ⟨0x80, readOnly⟩
    | 0x100000002 => some ⟨0xff, readOnly⟩
    | 0x100000003 => some ⟨0x41, readOnly⟩
    | 0x100000004 | 0x100000005 | 0x100000006 | 0x100000007 | 0x100000008 =>
        some ⟨0, readOnly⟩
    | 0x100000009 => some ⟨0x5a, readOnly⟩
    | _ => none

def declared : CallResources.Domain.Initial :=
  ⟨supplied, 7, 7, 10, 4096, [0xc3], 65544, 8192⟩

theorem original_facts : CallResources.Domain.Facts declared :=
  CallResources.Domain.check_sound (by decide +kernel)

def adopted : Borrowing.State :=
  { (CallResources.Domain.shared declared) with
    resources := Ownership.install
      (CallResources.Domain.shared declared).resources supplied 7 ⟨0x100000001, 9⟩ }

theorem adopted_valid : Borrowing.WellFormed adopted :=
  Borrowing.mutate_wellFormed _ (.adopt 7 ⟨0x100000001, 9⟩) (adopted, some ⟨2, 0⟩)
    (CallResources.Domain.shared_valid original_facts) (by rfl)

def shared : Borrowing.State := Borrowing.installLoan adopted
  ⟨⟨2, 0⟩, 7, Threads.principal 10, ⟨0x100000001, 8⟩⟩

theorem shared_valid : Borrowing.WellFormed shared :=
  (Borrowing.readBorrow_wellFormed _ 7 ⟨2, 0⟩ (Threads.principal 10) ⟨0x100000001, 8⟩
    (shared, 2) adopted_valid (by rfl)).1

def values : List Byte := [0x80, 0xff, 0x41, 0, 0, 0, 0, 0]

def resource : Resources Grading.ByteScan.spec :=
  ⟨shared, CallResources.Domain.call declared, ⟨0x100000001, values⟩, fun _ => 2⟩

theorem admitted : ResourceContract resource shared := by
  refine ⟨⟨shared_valid, ⟨_, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩,
    original_facts.code, original_facts.stack, original_facts.returnCanonical,
    original_facts.stackBound, original_facts.postStackCanonical⟩, ?_, ?_⟩
  · intro buffer member
    have same : buffer = ⟨0x100000001, values⟩ := by
      simpa [Grading.ByteScan.spec, resource] using member
    subst buffer
    refine ⟨by decide, ?_⟩
    intro index byte present
    match index with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 =>
      simp [values] at present
      subst byte
      rfl
    | index + 8 => simp [values] at present
  · intro buffer member _
    have same : buffer = ⟨0x100000001, values⟩ := by
      simpa [Grading.ByteScan.spec, resource] using member
    subst buffer
    exact ⟨_, rfl, rfl, rfl⟩

/-- Every final byte of the complete DATA8 span derives present live authority,
canonicality and actual read success through the new resource adapter. -/
theorem final_byte_current :
    ∃ identifier loan value,
      Borrowing.authorize shared (Threads.principal 10) identifier = .ok loan ∧
      loan.region.Contains 0x100000008 ∧ canonical 0x100000008 = true ∧
      readDataByte (toMemory shared.resources.space) 0x100000008 = .ok value := by
  have footprint : DataRead (Grading.ByteScan.spec.buffers resource.value)
      ⟨.data, 0x100000001, 8⟩ := by
    refine ⟨rfl, ⟨0x100000001, values⟩, by simp [Grading.ByteScan.spec, resource], ?_⟩
    unfold Buffer.Contains
    decide
  exact admitted.dataRead_bytes footprint (offset := 7) (by decide)

/-- Readable adjacent RAM does not extend either the raw permitted footprint
or the manager's actual loan. This catches an end-address-only/prefix check. -/
theorem readable_neighbor_denied :
    loadDWord (toMemory shared.resources.space) 0x100000006 = .ok 0x5a000000 ∧
    Borrowing.loadWord shared (Threads.principal 10) 2 0x100000006 = .error .outsideLoan ∧
    ¬ReadAllowed resource ⟨.data, 0x100000006, 4⟩ := by
  refine ⟨rfl, rfl, ?_⟩
  intro allowed
  rcases allowed with stack | data
  · cases stack.1
  · obtain ⟨_, buffer, member, span⟩ := data.1
    have same : buffer = ⟨0x100000001, values⟩ := by
      simpa [Grading.ByteScan.spec, resource] using member
    subst buffer
    have outside : ¬(Buffer.mk 0x100000001 values).Contains 0x100000006 4 := by
      unfold Buffer.Contains
      decide
    exact outside span

/-- The original stack loan cannot be moved by changing the machine RSP,
although that replacement address is readable and lies inside the data loan. -/
theorem replacement_stack_denied : ¬ReadAllowed resource ⟨.stack, 0x100000001, 8⟩ := by
  intro allowed
  rcases allowed with stack | data
  · have address := stack.2.1
    have different : (0x100000001 : Word) ≠ resource.call.stack := by decide
    exact different address
  · cases data.1.1

def ended : Borrowing.State :=
  { shared with loans := fun query => if query = 2 then none else shared.loans query }

/-- Revocation uses the real borrowing API and changes no memory. A stale
snapshot and complete readable RAM cannot reestablish the required current loan. -/
theorem revoked_snapshot_denied :
    Borrowing.finishLoan shared (Threads.principal 10) 2 = .ok ended ∧
    toMemory ended.resources.space = toMemory shared.resources.space ∧
    ¬ResourceContract resource ended := by
  refine ⟨rfl, rfl, ?_⟩
  intro contract
  obtain ⟨loan, live, _, _⟩ := contract.inputs ⟨0x100000001, values⟩
    (by simp [Grading.ByteScan.spec, resource]) (by decide)
  change none = some loan at live
  cases live

-- Two overlapping read-only input spans are issued from the SAME allocation.
-- There is no input-input or input-code disjointness condition in this API.
def overlapShared : Borrowing.State := Borrowing.installLoan shared
  ⟨⟨2, 0⟩, 7, Threads.principal 10, ⟨0x100000003, 4⟩⟩

theorem overlap_valid : Borrowing.WellFormed overlapShared :=
  (Borrowing.readBorrow_wellFormed _ 7 ⟨2, 0⟩ (Threads.principal 10) ⟨0x100000003, 4⟩
    (overlapShared, 3) shared_valid (by rfl)).1

def twoSpec : Spec := { Grading.ByteScan.spec with
  buffers input := [⟨input.base, input.values⟩, ⟨input.base + 2, input.values.drop 2 |>.take 4⟩] }

def twoResources : Resources twoSpec :=
  ⟨overlapShared, resource.call, resource.value,
    fun buffer => if buffer.base = 0x100000001 then 2 else 3⟩

theorem overlapping_buffers_admitted : ResourceContract twoResources overlapShared := by
  have first := admitted.buffers ⟨0x100000001, values⟩
    (by simp [Grading.ByteScan.spec, resource])
  refine ⟨⟨overlap_valid, ⟨_, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩,
    admitted.call.code, admitted.call.stack, admitted.call.returnCanonical,
    admitted.call.stackBound, admitted.call.postStackCanonical⟩, ?_, ?_⟩
  · intro buffer member
    have cases : buffer = ⟨0x100000001, values⟩ ∨ buffer = ⟨0x100000003, [0x41, 0, 0, 0]⟩ := by
      simpa [twoSpec, twoResources, resource, values] using member
    rcases cases with rfl | rfl
    · exact first
    · refine ⟨by decide, ?_⟩
      intro index byte present
      match index with
      | 0 | 1 | 2 | 3 => simp at present; subst byte; rfl
      | index + 4 => simp at present
  · intro buffer member _
    have cases : buffer = ⟨0x100000001, values⟩ ∨ buffer = ⟨0x100000003, [0x41, 0, 0, 0]⟩ := by
      simpa [twoSpec, twoResources, resource, values] using member
    rcases cases with rfl | rfl
    · exact ⟨_, rfl, rfl, rfl⟩
    · exact ⟨_, rfl, rfl, rfl⟩

/-- Code is a compatible read-only buffer and may reuse its original loan ID.
This quantifies all original call resources, rather than assigning a loan. -/
theorem code_alias_admitted (call : CallResources.Call) (shared : Borrowing.State)
    (original : CallResources.Contract call shared) :
    let aliasResource : Resources Grading.ByteScan.spec :=
      ⟨shared, call, ⟨call.code, call.bytes⟩, fun _ => call.codeLoan⟩
    ResourceContract aliasResource shared := by
  dsimp only
  refine ⟨original, ?_, ?_⟩
  · intro buffer member
    have same : buffer = ⟨call.code, call.bytes⟩ := by
      simpa [Grading.ByteScan.spec] using member
    subst buffer
    exact original.code.readable
  · intro buffer member _
    have same : buffer = ⟨call.code, call.bytes⟩ := by
      simpa [Grading.ByteScan.spec] using member
    subst buffer
    exact original.codeLoan

-- Independent expected answers challenge earliest versus later duplicate NULs,
-- unsigned high bytes, absent NUL, and n=0. These exercise spec.result itself.
theorem only_first_nul (result : Word) :
    Grading.ByteScan.spec.result ⟨0, [0x80, 0xff, 0, 0x41, 0]⟩ result ↔ result = 2 := by
  have reference : Grading.ByteScan.BoundedNulLength [0x80, 0xff, 0, 0x41, 0] 2 := by
    refine ⟨by decide, ?_, by decide⟩
    intro index inside
    match index with
    | 0 | 1 => decide
    | index + 2 => omega
  constructor
  · intro actual
    exact BitVec.eq_of_toNat_eq (Grading.ByteScan.BoundedNulLength.unique actual reference)
  · rintro rfl
    exact reference

theorem no_nul_returns_bound (result : Word) :
    Grading.ByteScan.spec.result ⟨0, [0x80, 0xff, 0x41]⟩ result ↔ result = 3 := by
  have reference : Grading.ByteScan.BoundedNulLength [0x80, 0xff, 0x41] 3 := by
    refine ⟨by decide, ?_, by decide⟩
    intro index inside
    match index with
    | 0 | 1 | 2 => decide
    | index + 3 => omega
  constructor
  · intro actual
    exact BitVec.eq_of_toNat_eq (Grading.ByteScan.BoundedNulLength.unique actual reference)
  · rintro rfl
    exact reference

/-- Low views accept the native C unsigned-char and low32 arguments even with
nonzero discarded upper bits; full64 still distinguishes the complete word. -/
theorem low_views_leave_upper_bits :
    Argument.Holds (.low8 0xff) 0xa55a1234567800ff ∧
    Argument.Holds (.low32 0x12345678) 0xa55a00ff12345678 ∧
    ¬Argument.Holds (.word64 0x12345678) 0xa55a00ff12345678 := by
  unfold Argument.Holds PureCall.Argument.Holds
  decide

end EDSL.Tests.BufferCallResources
