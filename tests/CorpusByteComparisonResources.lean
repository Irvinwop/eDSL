/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.ByteComparisonResources

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.CorpusByteComparisonResources
open X86 OS OS.AddressSpace BufferCall Corpus.V1 ByteComparisonResources

/-- A different authentic symbol in the same ELF is still the wrong requested
name. This exercises complete-file metadata authentication. -/
theorem wrong_name_rejected (compiler : Compiler) :
    (ByteComparisonWindows.input compiler).check (ByteComparisonWindows.file compiler)
      ByteScanWindows.name = false := by
  cases accepted : (ByteComparisonWindows.input compiler).check (ByteComparisonWindows.file compiler)
      ByteScanWindows.name with
  | false => rfl
  | true =>
    have wrong := (ELF.FunctionSymbol.checked_sound accepted).2.1.2.2.1
    have original := (ELF.FunctionSymbol.checked_sound (ByteScanWindows.checked compiler)).2.1.2.2.1
    change (ByteComparisonWindows.input compiler).metadata.matches ByteScanWindows.name =
      [(ByteScanWindows.function compiler).occurrence] at original
    have same := List.singleton_inj.mp (original.symm.trans wrong)
    have index := congrArg ELF.FunctionSymbol.Occurrence.index same
    have different : (ByteScanWindows.function compiler).occurrence.index ≠
        (ByteComparisonWindows.function compiler).occurrence.index := by
      cases compiler <;> decide +kernel
    exact False.elim (different index)

def shifted (compiler : Compiler) : Corpus.FunctionInput :=
  { ByteComparisonWindows.input compiler with function :=
    { ByteComparisonWindows.function compiler with window :=
      { (ByteComparisonWindows.function compiler).window with address :=
        (ByteComparisonWindows.function compiler).window.address + 1 } } }

/-- Correct file, name and bytes do not excuse a displaced function entry. -/
theorem shifted_rejected (compiler : Compiler) :
    (shifted compiler).check (ByteComparisonWindows.file compiler) ByteComparisonWindows.name = false := by
  cases accepted : (shifted compiler).check (ByteComparisonWindows.file compiler)
      ByteComparisonWindows.name with
  | false => rfl
  | true =>
    have address := (ELF.FunctionSymbol.checked_mapping accepted).1
    change (ByteComparisonWindows.function compiler).occurrence.symbol.value + 1 =
      (ByteComparisonWindows.function compiler).occurrence.symbol.value at address
    omega

/-- The final BSS cell tests zero-fill retention and writable/NX permissions,
well outside the admitted function. A text-only world cannot pass. -/
theorem retained_bss (compiler : Compiler) :
    readDataByte (witness compiler).initial.memory 0x40910f = .ok 0 ∧
      (witness compiler).initial.memory.writable 0x40910f = true ∧
      (witness compiler).initial.memory.executable 0x40910f = false := by
  have original : (installed compiler).space.cells 0x40910f = some ⟨0, readWrite⟩ := by
    rw [installed_seed]
    cases compiler <;> buffer_resource_kernel_rfl
  have present := installed_frame compiler original
  change readDataByte (toMemory (resources compiler).shared.resources.space) 0x40910f = _ ∧
    (toMemory (resources compiler).shared.resources.space).writable 0x40910f = _ ∧
    (toMemory (resources compiler).shared.resources.space).executable 0x40910f = _
  refine ⟨?_, ?_, ?_⟩ <;> simp only [readDataByte, toMemory, present] <;> buffer_resource_kernel_rfl

theorem wrong_entry_rejected (compiler : Compiler) :
    ¬ ResourcePre spec (ByteComparisonWindows.bytes compiler) (resources compiler)
      { (witness compiler).initial with rip := entry compiler + 1 } := by
  intro admitted
  have different : entry compiler + 1 ≠ entry compiler := by
    cases compiler <;> decide +kernel
  exact different admitted.entry

/-- Both pointers are full-width ABI bindings. Changing only one side cannot
borrow the other side's argument or its compatible read authority. -/
theorem wrong_left_pointer_rejected (compiler : Compiler) (pointer : Word)
    (different : pointer ≠ value.leftBase) :
    ¬ ResourcePre spec (ByteComparisonWindows.bytes compiler) (resources compiler)
      { (witness compiler).initial with registers := fun register =>
        if register = .rdi then pointer else (witness compiler).initial.registers register } := by
  intro admitted
  exact different (admitted.arguments (0 : Fin 6) (.word64 value.leftBase) rfl)

theorem wrong_right_pointer_rejected (compiler : Compiler) (pointer : Word)
    (different : pointer ≠ value.rightBase) :
    ¬ ResourcePre spec (ByteComparisonWindows.bytes compiler) (resources compiler)
      { (witness compiler).initial with registers := fun register =>
        if register = .rsi then pointer else (witness compiler).initial.registers register } := by
  intro admitted
  exact different (admitted.arguments (1 : Fin 6) (.word64 value.rightBase) rfl)

/-- A high-bit-only count change must fail too: RDX is not truncated to 32. -/
theorem wrong_count_rejected (compiler : Compiler) (count : Word)
    (different : count ≠ BitVec.ofNat 64 value.left.length) :
    ¬ ResourcePre spec (ByteComparisonWindows.bytes compiler) (resources compiler)
      { (witness compiler).initial with registers := fun register =>
        if register = .rdx then count else (witness compiler).initial.registers register } := by
  intro admitted
  exact different (admitted.arguments (2 : Fin 6) (.word64 (BitVec.ofNat 64 value.left.length)) rfl)

theorem replacement_stack_rejected (compiler : Compiler) (stack : Word)
    (different : stack ≠ layout.stack) :
    ¬ ResourcePre spec (ByteComparisonWindows.bytes compiler) (resources compiler)
      { (witness compiler).initial with registers := fun register =>
        if register = .rsp then stack else (witness compiler).initial.registers register } := by
  intro admitted
  exact different admitted.stack

/-- A forged final right byte is rejected against actual current RAM, despite
the genuine right loan and the left snapshot remaining available. -/
theorem wrong_right_snapshot_rejected (compiler : Compiler) :
    ¬ ResourceContract (spec := spec)
      { resources compiler with value :=
        (⟨value.leftBase, value.rightBase, value.left, [0x42, 0, 1]⟩ : Grading.ByteComparison.Input) }
      (resources compiler).shared := by
  intro admitted
  have changed := ((Grading.ByteComparison.resourceContract_iff _ _).mp admitted).2.2.1
  have actual := (right_snapshot compiler).2 2 0 rfl
  have wrong := changed.2 2 1 rfl
  have impossible : (0 : Byte) = 1 := Except.ok.inj (actual.symm.trans wrong)
  exact (by decide +kernel : (0 : Byte) ≠ 1) impossible

/-- The last right byte is readable RAM outside the old loan. Readability
alone must not be mistaken for authority on that byte. -/
theorem old_last_byte_denied (compiler : Compiler) :
    ∃ loan,
      Borrowing.authorize (resources compiler).shared (Threads.principal layout.worker)
        ((ByteScanResources.resources compiler).inputLoan ByteScanResources.buffer) = .ok loan ∧
      ¬ loan.region.Contains 0x10003 ∧
      readDataByte (toMemory (resources compiler).shared.resources.space) 0x10003 = .ok 0 := by
  obtain ⟨loan, live, borrower, region⟩ := ByteScanResources.buffer_held compiler
  refine ⟨loan, ?_, ?_, ?_⟩
  · simp [Borrowing.authorize, original_loans compiler live, borrower]
  · rw [region]
    decide +kernel
  · exact (right_snapshot compiler).2 2 0 rfl

/-- Reusing the old left loan for the new right descriptor must fail, even
though the snapshots overlap and the old loan has the same byte count. -/
theorem old_left_loan_rejected_for_right (compiler : Compiler) :
    ¬ ResourceContract
      { resources compiler with inputLoan := fun _ =>
          (ByteScanResources.resources compiler).inputLoan ByteScanResources.buffer }
      (resources compiler).shared := by
  intro admitted
  obtain ⟨loan, live, _, region⟩ := admitted.inputs right
    (by simp [taskID, Grading.BufferTask.registeredSpec, Grading.ByteComparison.spec,
      resources, right]) (by decide +kernel)
  obtain ⟨old, oldLive, _, oldRegion⟩ := ByteScanResources.buffer_held compiler
  have retained := original_loans compiler oldLive
  have same : loan = old := Option.some.inj (live.symm.trans retained)
  have bases := congrArg Region.base (region.symm.trans (same ▸ oldRegion))
  exact (by decide +kernel : right.base ≠ ByteScanResources.buffer.base) bases

/-- Every byte in the right span has authority through its actual issued
loan. This includes 0x10003, where the seed's three-byte loan stops. -/
theorem actual_right_span_authorized (compiler : Compiler) (index : Nat) (bound : index < 3) :
    ∃ loan byte,
      Borrowing.authorize (resources compiler).shared (Threads.principal layout.worker)
        ((resources compiler).inputLoan right) = .ok loan ∧
      loan.region.Contains (right.base + BitVec.ofNat 64 index) ∧
      readDataByte (toMemory (resources compiler).shared.resources.space)
        (right.base + BitVec.ofNat 64 index) = .ok byte := by
  obtain ⟨loan, live, borrower, region⟩ := right_held compiler
  have inside : index < right.bytes.length := bound
  refine ⟨loan, right.bytes[index], ?_, ?_, ?_⟩
  · simp [Borrowing.authorize, live, borrower]
  · rw [region]
    exact Buffer.offset_inside (right_snapshot compiler) inside
  · exact (right_snapshot compiler).2 index _ (List.getElem?_eq_getElem inside)

def ended (compiler : Compiler) : Borrowing.State :=
  { (resources compiler).shared with loans := fun query =>
    if query = (resources compiler).inputLoan right then none else (resources compiler).shared.loans query }

/-- A real finishLoan action revokes the right loan without changing any RAM,
allocation, epoch or permission; the resource contract must then fail. -/
theorem revoked_right_rejected (compiler : Compiler) :
    Borrowing.finishLoan (resources compiler).shared (Threads.principal layout.worker)
      ((resources compiler).inputLoan right) = .ok (ended compiler) ∧
    (ended compiler).resources = (resources compiler).shared.resources ∧
    ¬ ResourceContract (resources compiler) (ended compiler) := by
  obtain ⟨loan, live, borrower, _⟩ := right_held compiler
  refine ⟨?_, rfl, ?_⟩
  · simp [Borrowing.finishLoan, Borrowing.authorize, live, borrower, ended]
  · intro admitted
    obtain ⟨_, live, _, _⟩ := admitted.inputs right
      (by simp [taskID, Grading.BufferTask.registeredSpec, Grading.ByteComparison.spec,
        resources, right]) (by decide +kernel)
    simp [ended] at live

/-- The original private return slot remains frozen by its original loan,
so even the original owner cannot rewrite it while the call is current. -/
theorem caller_store_denied (compiler : Compiler) :
    Borrowing.mutate (resources compiler).shared
      (.store64 layout.callerOwner ⟨1, 0⟩ layout.stack 0) = .error .borrowed := by
  cases compiler <;> buffer_resource_kernel_rfl

def emptyResources (compiler : Compiler) (leftBase rightBase : Word) (unused : Buffer → Nat) :
    Resources spec :=
  { resources compiler with value := ⟨leftBase, rightBase, [], []⟩, inputLoan := unused }

def emptyMachine (compiler : Compiler) (leftBase rightBase : Word)
    (registers : Register → Word) (flags : Word) : X86.State :=
  { machine compiler registers flags with registers := fun register => match register with
      | .rdi => leftBase
      | .rsi => rightBase
      | .rdx => 0
      | other => (machine compiler registers flags).registers other }

/-- Zero count admits arbitrary unmapped/noncanonical pointers on BOTH sides
and any unused loan selector, with all original call and ABI checks intact. -/
theorem empty_pre (compiler : Compiler) (leftBase rightBase : Word) (unused : Buffer → Nat)
    (registers : Register → Word) (flags : Word) :
    ResourcePre spec (ByteComparisonWindows.bytes compiler)
      (emptyResources compiler leftBase rightBase unused)
      (emptyMachine compiler leftBase rightBase registers flags) := by
  refine ⟨⟨?_, rfl⟩, rfl, rfl, rfl, ?_, ?_⟩
  · exact Grading.ByteComparison.empty_resources _ _ (contract compiler).call leftBase rightBase unused
  · change 0 = 0 ∧ 0 < 2^64
    decide +kernel
  · exact (Grading.ByteComparison.bound_iff _ _).mpr ⟨rfl, rfl, rfl⟩

/-- Empty requests do not inspect either owner or ticket, and preserve the
exact current managed state rather than reconstructing a substitute world. -/
theorem empty_requests_ignored (compiler : Compiler) (leftBase rightBase : Word)
    (leftOwner rightOwner : Nat) (leftTicket rightTicket : Ownership.Ticket) :
    ∃ result,
      Corpus.ReadOnlyInputs.borrow (ready compiler).managed layout.worker
        [⟨leftOwner, leftTicket, ⟨leftBase, []⟩⟩, ⟨rightOwner, rightTicket, ⟨rightBase, []⟩⟩] =
          .ok result ∧ result.managed = (ready compiler).managed ∧ result.identifiers = [0, 0] := by
  apply Corpus.ReadOnlyInputs.all_empty
  intro request member
  simp at member
  rcases member with rfl | rfl <;> rfl

#print axioms wrong_name_rejected
#print axioms shifted_rejected
#print axioms retained_bss
#print axioms wrong_entry_rejected
#print axioms wrong_left_pointer_rejected
#print axioms wrong_right_pointer_rejected
#print axioms wrong_count_rejected
#print axioms replacement_stack_rejected
#print axioms wrong_right_snapshot_rejected
#print axioms old_last_byte_denied
#print axioms old_left_loan_rejected_for_right
#print axioms actual_right_span_authorized
#print axioms revoked_right_rejected
#print axioms caller_store_denied
#print axioms empty_pre
#print axioms empty_requests_ignored
end EDSL.Tests.CorpusByteComparisonResources
#audit_edsl
