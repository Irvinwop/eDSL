/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.StoreReturnValue64.Correctness
import EDSL.Grading.StoreReturnValue64.Domain
import EDSL.Audit

set_option warningAsError true
set_option maxRecDepth 4096

namespace EDSL.Tests.GradingStoreReturnValue64Policy
open EDSL EDSL.X86 EDSL.X86.Sequential EDSL.OS EDSL.Grading.Trace
open EDSL.OS.WordResources64 EDSL.Grading.StoreReturnValue64
namespace D
export EDSL.Grading.StoreReturnValue64.Domain (initial call shared resource arbitrary_current)
end D

-- MOV [RDX],ESI; RET, with an eight-byte admitted code loan.
private def narrowBytes : List Byte := [0x89, 0x32, 0xc3, 0, 0, 0, 0, 0]
private def narrowInitial (offset : Nat) : State :=
  D.initial narrowBytes 0 (fun _ => 262144 + BitVec.ofNat 64 offset)

private theorem narrow_current (offset : Nat) :
    Current (D.call narrowBytes) (D.shared narrowBytes) (narrowInitial offset) :=
  (D.arbitrary_current narrowBytes (by decide) (by decide) 0
    (fun _ => 262144 + BitVec.ofNat 64 offset)).1

private theorem narrow_decoded (offset : Nat) :
    Sequential.decodeAt (narrowInitial offset) = .ok (.storeMem32 (.base .rdx) .rsi) := by
  have raw := EDSL.Grading.StoreReturnValue64.Domain.raw_pre narrowBytes (by decide) (by decide) 0
    (fun _ => 262144 + BitVec.ofNat 64 offset)
  exact decodeAt_transport
    (code_fetch_transport raw.code (by decide) 0 (by decide) (narrowInitial offset) rfl rfl) rfl

private theorem subspan (offset : Nat) (bound : offset ≤ 4) :
    Borrowing.Subregion (AddressSpace.wordRegion (262144 + BitVec.ofNat 64 offset))
      (AddressSpace.qwordRegion 262144) := by
  have small : offset < 2^64 := by omega
  have total : 262144 + offset < 2^64 := by omega
  change 262144 ≤ ((262144 : Word) + BitVec.ofNat 64 offset).toNat ∧
    ((262144 : Word) + BitVec.ofNat 64 offset).toNat + 4 ≤ 262144 + 8
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    show (262144 : Word).toNat = 262144 from rfl]
  rw [Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt total]
  omega

/-- Every starting offset 0..4 executes a REAL checked narrow mutation, even
when writing the existing value. This exercises decoding, permission subset,
borrow gate, machine coupling, wide frame and usable returned wide authority. -/
theorem all_subword_offsets_checked (offset : Nat) (bound : offset ≤ 4) (af : Bool) :
    ∃ evolved,
      Borrowing.mutate (D.shared narrowBytes) (.store 11 ⟨4, 0⟩
        (262144 + BitVec.ofNat 64 offset) 0) = .ok (evolved, none) ∧
      step af (narrowInitial offset) =
        .ok ⟨.next (storeAfterLength (narrowInitial offset) evolved 2), []⟩ ∧
      Current (D.call narrowBytes) evolved (storeAfterLength (narrowInitial offset) evolved 2) ∧
      Frame 262144 (D.shared narrowBytes) evolved ∧
      loadDWord (AddressSpace.toMemory evolved.resources.space)
        (262144 + BitVec.ofNat 64 offset) = .ok 0 ∧
      (∀ identifier loan, (D.shared narrowBytes).loans identifier = some loan →
        ∀ query, loan.region.Contains query →
          evolved.resources.space.cells query = (D.shared narrowBytes).resources.space.cells query) ∧
      (∀ next : Word, ∃ world,
        Borrowing.mutate evolved (.store64 11 ⟨4, 0⟩ 262144 next) = .ok (world, none)) ∧
      SpanEffect 11 ⟨4, 0⟩ 262144 (D.shared narrowBytes) (narrowInitial offset)
        (.storeMem32 (.base .rdx) .rsi)
        ⟨.next (storeAfterLength (narrowInitial offset) evolved 2), []⟩ evolved := by
  have decoded : Sequential.decodeAt (narrowInitial offset) =
      .ok (.storeMem32 (.base .rdx) .rsi) := narrow_decoded offset
  have intent : Sequential.Instruction.storeIntent (.storeMem32 (.base .rdx) .rsi)
      (narrowInitial offset) = some (262144 + BitVec.ofNat 64 offset, 0) := rfl
  obtain ⟨evolved, stored, actual, current, effect, frame, loans⟩ :=
    current_store32_step (narrow_current offset) decoded intent (subspan offset bound) af
  exact ⟨evolved, stored, actual, current, frame, effect.readback, loans,
    (fun next => current_store64_enabled current next), .store32 intent (subspan offset bound) stored⟩

/-- DATA4 permission follows every complete target subspan; no target loan is
needed, including the unaligned offsets 1,2,3 and final valid offset4. -/
theorem all_subword_offsets_readable (offset : Nat) (bound : offset ≤ 4) :
    EDSL.Grading.StoreReturnValue64.ReadAllowed (D.call narrowBytes) (D.shared narrowBytes)
      (narrowInitial offset) ⟨.data, 262144 + BitVec.ofNat 64 offset, 4⟩ ∧
      OperandReadSucceeds (narrowInitial offset) ⟨.data, 262144 + BitVec.ofNat 64 offset, 4⟩ :=
  current_subword_read (narrow_current offset) (subspan offset bound)

private theorem crossing_forbidden :
    ¬RawEffect 262144 (narrowInitial 5) (.storeMem32 (.base .rdx) .rsi) := by
  intro effect
  have span := effect.store32_span rfl (show
    Sequential.Instruction.storeIntent (.storeMem32 (.base .rdx) .rsi) (narrowInitial 5) =
      some (262149, 0) from rfl) rfl
  have upper := span.2
  change 262149 + 4 ≤ 262144 + 8 at upper
  omega

/-- Byte8 is really readable/writable in this negative machine example, so
the offset5 rejection is the owned target boundary, not an inaccessible byte. -/
private def readableNeighbor : State :=
  { narrowInitial 5 with memory :=
    { (narrowInitial 5).memory with
      read := fun query => if query = 262152 then some 0 else (narrowInitial 5).memory.read query
      writable := fun query => if query = 262152 then true else (narrowInitial 5).memory.writable query } }

theorem crossing_rejected_despite_readable_neighbor :
    canStoreDWord readableNeighbor.memory 262149 = true ∧
      loadDWord readableNeighbor.memory 262149 = .ok 0 ∧
      (∃ after, step false readableNeighbor = .ok ⟨.next after, []⟩) ∧
      ¬RawEffect 262144 readableNeighbor (.storeMem32 (.base .rdx) .rsi) ∧
      (∀ shared observation evolved,
        ¬SpanEffect 11 ⟨4, 0⟩ 262144 shared readableNeighbor
          (.storeMem32 (.base .rdx) .rsi) observation evolved) := by
  have writable : canStoreDWord readableNeighbor.memory 262149 = true := by decide
  have forbidden : ¬RawEffect 262144 readableNeighbor (.storeMem32 (.base .rdx) .rsi) := by
    intro effect
    have span := effect.store32_span rfl (show
      Sequential.Instruction.storeIntent (.storeMem32 (.base .rdx) .rsi) readableNeighbor =
        some (262149, 0) from rfl) rfl
    have upper := span.2
    change 262149 + 4 ≤ 262144 + 8 at upper
    omega
  refine ⟨writable, rfl, ?_, forbidden, fun _ _ _ effect => forbidden effect.raw⟩
  have intent : Sequential.Instruction.storeIntent (.storeMem32 (.base .rdx) .rsi)
      readableNeighbor = some (262149, 0) := rfl
  have stored : storeDWord readableNeighbor.memory 262149 0 =
      .ok (writeDWordUnchecked readableNeighbor.memory 262149 0) := by
    unfold storeDWord
    rw [writable]
    rfl
  rw [step_eq_execute false (show Sequential.decodeAt readableNeighbor =
    .ok (.storeMem32 (.base .rdx) .rsi) from rfl), execute_storeIntent false intent, stored]
  exact ⟨_, rfl⟩

/-- Rejection applies to actual prefixes of both policies, even though current
wide ownership was admitted independently of the narrow store's decoding. -/
theorem crossing_policies_rejected :
    ¬RawPolicy narrowBytes (resourceInput (D.resource narrowBytes 0)) (narrowInitial 5) ∧
      ¬ResourcePolicy (D.resource narrowBytes 0) (narrowInitial 5) := by
  have decoded : Sequential.decodeAt (narrowInitial 5) = .ok (.storeMem32 (.base .rdx) .rsi) := rfl
  exact ⟨fun policy => policy.rejects_instruction ⟨fun _ => false, 0, [], .nil⟩ decoded crossing_forbidden,
    fun policy => policy.rejects_instruction ⟨fun _ => false, 0, [], .nil⟩ decoded crossing_forbidden⟩

/-- A current loan cannot extend the target's DATA4 boundary. This theorem
holds for every current world, including worlds with readable neighbors. -/
theorem crossing_read_rejected {call : Call} {shared : Borrowing.State} {before : State}
    (current : Current call shared before) (target : call.targetPointer = 262144) :
    ¬EDSL.Grading.StoreReturnValue64.ReadAllowed call shared before ⟨.data, 262149, 4⟩ := by
  intro allowed
  have inside : (AddressSpace.qwordRegion call.targetPointer).Contains 262149 := by
    rw [target]
    decide
  have upper := (readAllowed_subword_span current inside allowed).2
  rw [target] at upper
  change 262149 + 4 ≤ 262144 + 8 at upper
  omega

/-- After a real narrow store, code/stack/unrelated current held read-only
loans still authorize DATA reads. Their original cells and all loan metadata
remain on the same checked history. -/
theorem loan_reads_survive_checked_subword :
    ∃ evolved,
      Borrowing.mutate (D.shared narrowBytes) (.store 11 ⟨4, 0⟩ 262148 0) = .ok (evolved, none) ∧
      Frame 262144 (D.shared narrowBytes) evolved ∧
      EDSL.Grading.StoreReturnValue64.ReadAllowed (D.call narrowBytes) evolved
        (storeAfterLength (narrowInitial 4) evolved 2) ⟨.data, 4096, 8⟩ ∧
      EDSL.Grading.StoreReturnValue64.ReadAllowed (D.call narrowBytes) evolved
        (storeAfterLength (narrowInitial 4) evolved 2) ⟨.data, 65544, 4⟩ ∧
      EDSL.Grading.StoreReturnValue64.ReadAllowed (D.call narrowBytes) evolved
        (storeAfterLength (narrowInitial 4) evolved 2) ⟨.data, 131076, 8⟩ ∧
      (AddressSpace.toMemory evolved.resources.space).writable 4096 = false ∧
      (AddressSpace.toMemory evolved.resources.space).writable 131076 = false := by
  obtain ⟨evolved, stored, _, current, frame, _, _, _⟩ := all_subword_offsets_checked 4 (by decide) false
  have permission (identifier : Nat) (address : Word) (width : Nat)
      (authorized : Borrowing.authorize (D.shared narrowBytes) 11 identifier =
        .ok (Grading.Domain.loan narrowBytes identifier))
      (span : Borrowing.Subregion ⟨address, width⟩ (Grading.Domain.loan narrowBytes identifier).region) :
      ArrayResources.ReadPermission evolved (D.call narrowBytes).worker ⟨.data, address, width⟩ := by
    refine ⟨identifier, Grading.Domain.loan narrowBytes identifier, ?_, span⟩
    change Borrowing.authorize evolved 11 identifier = _
    simpa only [Borrowing.authorize, frame.loans] using authorized
  have code := current_loan_read current (Or.inr rfl) (permission 0 4096 8 rfl (by decide))
  have stack := current_loan_read current (Or.inl rfl) (permission 1 65544 4 rfl (by decide))
  have other := current_loan_read current (Or.inr rfl) (permission 2 131076 8 rfl (by decide))
  refine ⟨evolved, stored, frame, code.1, stack.1, other.1, ?_, ?_⟩
  · have outside : ¬(AddressSpace.qwordRegion 262144).Contains 4096 := by decide
    have cells := frame.outside 4096 outside
    change (AddressSpace.toMemory evolved.resources.space).writable 4096 = false
    simp only [AddressSpace.toMemory, cells]
    rfl
  · have outside : ¬(AddressSpace.qwordRegion 262144).Contains 131076 := by decide
    have cells := frame.outside 131076 outside
    simp only [AddressSpace.toMemory, cells]
    rfl

/-- A successful four-byte loan load cannot be relabeled as eight bytes. -/
theorem recorded_width_is_truthful :
    loadDWord (narrowInitial 0).memory 131084 = .ok 11 ∧
      loadQWord (narrowInitial 0).memory 131084 = .error (.inaccessibleData 131088) ∧
      ¬EDSL.Grading.StoreReturnValue64.ReadAllowed (D.call narrowBytes) (D.shared narrowBytes)
        (narrowInitial 0) ⟨.data, 131084, 8⟩ := by
  have failed : loadQWord (narrowInitial 0).memory 131084 = .error (.inaccessibleData 131088) := rfl
  refine ⟨rfl, failed, ?_⟩
  rintro (target | ⟨_, _, value, loaded⟩)
  · have same := target.1
    change (131084 : Word) = 262144 at same
    exact (by decide : (131084 : Word) ≠ 262144) same
  · rw [failed] at loaded
    cases loaded

private theorem forbidden_policies {bytes : List Byte} {instruction : Sequential.Instruction}
    (decoded : Sequential.decodeAt (D.initial bytes) = .ok instruction)
    (forbidden : ¬RawEffect 262144 (D.initial bytes) instruction) :
    ¬RawPolicy bytes (resourceInput (D.resource bytes)) (D.initial bytes) ∧
      ¬ResourcePolicy (D.resource bytes) (D.initial bytes) :=
  ⟨fun policy => policy.rejects_instruction ⟨fun _ => false, 0, [], .nil⟩ decoded forbidden,
    fun policy => policy.rejects_instruction ⟨fun _ => false, 0, [], .nil⟩ decoded forbidden⟩

theorem exchange_rejected :
    ¬RawPolicy [0x87, 0x07] (resourceInput (D.resource [0x87, 0x07])) (D.initial [0x87, 0x07]) ∧
      ¬ResourcePolicy (D.resource [0x87, 0x07]) (D.initial [0x87, 0x07]) :=
  forbidden_policies (instruction := .legacy .exchangeEaxRdi) rfl
    (fun effect => effect.rejects_unsupported rfl rfl rfl)

theorem locked_add_rejected :
    ¬RawPolicy [0xf0, 0x0f, 0xc1, 0x07]
      (resourceInput (D.resource [0xf0, 0x0f, 0xc1, 0x07])) (D.initial [0xf0, 0x0f, 0xc1, 0x07]) ∧
      ¬ResourcePolicy (D.resource [0xf0, 0x0f, 0xc1, 0x07]) (D.initial [0xf0, 0x0f, 0xc1, 0x07]) :=
  forbidden_policies (instruction := .legacy .fetchAddEaxRdi) rfl
    (fun effect => effect.rejects_unsupported rfl rfl rfl)

theorem syscall_rejected :
    ¬RawPolicy [0x0f, 0x05] (resourceInput (D.resource [0x0f, 0x05])) (D.initial [0x0f, 0x05]) ∧
      ¬ResourcePolicy (D.resource [0x0f, 0x05]) (D.initial [0x0f, 0x05]) :=
  forbidden_policies (instruction := .legacy .syscall) rfl
    (fun effect => effect.rejects_unsupported rfl rfl rfl)

/-- The wider opcode has no exemption for a foreign destination. This uses
the actual decoded instruction with current target authority still present. -/
theorem foreign64_policies_rejected :
    ¬RawPolicy [0x48, 0x89, 0x32, 0xc3]
      (resourceInput (D.resource [0x48, 0x89, 0x32, 0xc3]))
      (D.initial [0x48, 0x89, 0x32, 0xc3]) ∧
      ¬ResourcePolicy (D.resource [0x48, 0x89, 0x32, 0xc3])
        (D.initial [0x48, 0x89, 0x32, 0xc3]) := by
  apply forbidden_policies (instruction := .storeMem64 (.base .rdx) .rsi) rfl
  intro effect
  have same := effect.store64_target rfl rfl (show
    Sequential.Instruction.storeIntent64 (.storeMem64 (.base .rdx) .rsi)
      (D.initial [0x48, 0x89, 0x32, 0xc3]) = some (0xfedcba9876543210, 0xfeedface89abcdef) from rfl)
  exact (by decide : (0xfedcba9876543210 : Word) ≠ 262144) same

/-- The old strict64 policy still excludes the very same admitted, same-value
narrow instruction that the new span policy permits. -/
theorem strict64_still_rejects_narrow :
    ¬EDSL.StoreLoad64.ResourcePolicy (D.resource narrowBytes 0) (narrowInitial 0) := by
  rintro ⟨Inv, start, advance⟩
  obtain ⟨_, instruction, decoded, enabled⟩ := advance (D.shared narrowBytes) (narrowInitial 0) start
  have actual : Sequential.decodeAt (narrowInitial 0) = .ok (.storeMem32 (.base .rdx) .rsi) := rfl
  have same := Except.ok.inj (decoded.symm.trans actual)
  cases same
  obtain ⟨_, _, _, _, effect, _⟩ := enabled false
  cases effect.2 with
  | readOnly allowed => cases allowed
  | store64 intent _ => cases intent

end EDSL.Tests.GradingStoreReturnValue64Policy

#print axioms EDSL.Grading.StoreReturnValue64.raw_semantics
#print axioms EDSL.Grading.StoreReturnValue64.resource_semantics
#print axioms EDSL.OS.WordResources64.current_store32_step
#print axioms EDSL.Grading.StoreReturnValue64.current_loan_read
#print axioms EDSL.Tests.GradingStoreReturnValue64Policy.all_subword_offsets_checked
#print axioms EDSL.Tests.GradingStoreReturnValue64Policy.loan_reads_survive_checked_subword

#audit_edsl
