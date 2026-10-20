/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.ByteScanResources

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.CorpusByteScanResources
open X86 OS OS.AddressSpace BufferCall Corpus.V1
namespace Windows
open ByteScanWindows

/-- Keep the authentic ELF, selected symbol and code, but request `other`.
A checker which ignores the caller's requested name must fail this test. -/
theorem wrong_name_rejected (compiler : Compiler) :
    (input compiler).check (file compiler) [0x6f, 0x74, 0x68, 0x65, 0x72] = false := by
  cases accepted : (input compiler).check (file compiler) [0x6f, 0x74, 0x68, 0x65, 0x72] with
  | false => rfl
  | true =>
    have contract := (ELF.FunctionSymbol.checked_sound accepted).2.1
    have absent : (input compiler).metadata.matches [0x6f, 0x74, 0x68, 0x65, 0x72] = [] := by
      cases compiler <;> decide +kernel
    have unique := contract.2.2.1
    rw [absent] at unique
    cases unique

def shifted (compiler : Compiler) : Corpus.FunctionInput :=
  { input compiler with function := { function compiler with
      window := { (function compiler).window with address := (function compiler).window.address + 1 } } }

/-- Correct body/name/offset cannot excuse the wrong actual ELF entry. -/
theorem shifted_rejected (compiler : Compiler) :
    (shifted compiler).check (file compiler) name = false := by
  cases accepted : (shifted compiler).check (file compiler) name with
  | false => rfl
  | true =>
    have address := (ELF.FunctionSymbol.checked_mapping accepted).1
    cases compiler with
    | defaultGCC => change 4206433 = 4206432 at address; omega
    | defaultClang => change 4199585 = 4199584 at address; omega

def changedLast (compiler : Compiler) : Corpus.FunctionInput :=
  { input compiler with bytes := (bytes compiler).set ((bytes compiler).length - 1) 0x90 }

/-- A mutation of the LAST symbol byte is rejected by file-source equality;
checking only the prefix or instruction entry bytes would miss this defect. -/
theorem changed_last_rejected (compiler : Compiler) :
    (changedLast compiler).check (file compiler) name = false := by
  cases accepted : (changedLast compiler).check (file compiler) name with
  | false => rfl
  | true =>
    have original := (ELF.FunctionSymbol.checked_sound (checked compiler)).2.2.2.source
    have mutated := (ELF.FunctionSymbol.checked_sound accepted).2.2.2.source
    change ((file compiler).drop (function compiler).window.offset).take
      (bytes compiler).length = bytes compiler at original
    change ((file compiler).drop (function compiler).window.offset).take
      ((bytes compiler).set ((bytes compiler).length - 1) 0x90).length = _ at mutated
    rw [List.length_set, original] at mutated
    have last := congrArg List.getLast? mutated
    have different : (bytes compiler).getLast? ≠
        ((bytes compiler).set ((bytes compiler).length - 1) 0x90).getLast? := by
      cases compiler <;> decide +kernel
    exact False.elim (different last)

/-- Complete-file admission cannot be replaced by a small extracted body,
even when that body is exactly the requested symbol's bytes. -/
theorem body_is_not_file (compiler : Compiler) :
    (input compiler).check (bytes compiler) name = false := by
  cases accepted : (input compiler).check (bytes compiler) name with
  | false => rfl
  | true =>
    have bound := (ELF.FunctionSymbol.checked_sound accepted).2.2.2.bounds.2.2.2
    cases compiler with
    | defaultGCC => change 12128 + 35 ≤ 35 at bound; omega
    | defaultClang => change 5280 + 34 ≤ 34 at bound; omega

/-- Corrupting the ELF magic OUTSIDE the function cannot be admitted using
unchanged function bytes, metadata hints and offsets. -/
theorem header_tamper_rejected (compiler : Compiler) :
    (input compiler).check ((file compiler).set 0 0) name = false := by
  cases accepted : (input compiler).check ((file compiler).set 0 0) name with
  | false => rfl
  | true =>
    have layout := (ELF.FunctionSymbol.checked_sound accepted).2.2.1
    have magic := (layout.header ⟨0, 4, 0x464c457f⟩ (by
      cases compiler <;> decide +kernel)).2
    have different :
        (((file compiler).set 0 0).drop 0 |>.take 4).foldr
          (fun byte rest => byte.toNat + rest * 256) 0 ≠ 0x464c457f := by
      cases compiler <;> decide +kernel
    exact False.elim (different magic)

/-- The shared full ELF binding retains the final RET, beyond Clang's NOP9
and GCC's ENDBR64, at each actual final symbol-file position. -/
theorem last_file_byte (compiler : Compiler) :
    (file compiler)[(function compiler).window.offset + (bytes compiler).length - 1]? = some 0xc3 := by
  have selected := (ELF.FunctionSymbol.checked_sound (checked compiler)).2.2.2
  have present : (bytes compiler)[(bytes compiler).length - 1]? = some 0xc3 := by
    cases compiler <;> decide +kernel
  have last := selected.file_byte present
  cases compiler <;> exact last

end Windows
open ByteScanResources

/-- Current memory still contains the ELF header OUTSIDE the selected window.
This challenges replacing the installed file with a small synthetic code map. -/
theorem retained_header (compiler : Compiler) (registers : Register → Word) (flags : Word) :
    readDataByte (machine compiler registers flags).memory 0x400000 = .ok 0x7f ∧
    (machine compiler registers flags).memory.writable 0x400000 = false := by
  have original : (installed compiler).space.cells 0x400000 = some ⟨0x7f, readOnly⟩ := by
    cases compiler <;> buffer_resource_kernel_rfl
  have present := installed_frame compiler original
  constructor <;> simp only [machine, readDataByte, toMemory, present] <;> rfl

theorem wrong_entry_rejected (compiler : Compiler) (registers : Register → Word) (flags : Word) :
    ¬ResourcePre Grading.ByteScan.spec (ByteScanWindows.bytes compiler) (resources compiler)
      { machine compiler registers flags with rip := entry compiler + 1 } := by
  intro admitted
  have address := admitted.entry
  have impossible : entry compiler + 1 ≠ entry compiler := by
    cases compiler <;> decide +kernel
  exact impossible address

theorem wrong_pointer_rejected (compiler : Compiler) (registers : Register → Word)
    (flags pointer : Word) (different : pointer ≠ value.base) :
    ¬ResourcePre Grading.ByteScan.spec (ByteScanWindows.bytes compiler) (resources compiler)
      { machine compiler registers flags with registers := fun register =>
          if register = .rdi then pointer else (machine compiler registers flags).registers register } := by
  intro admitted
  have binding := admitted.arguments ⟨0, by decide⟩ (.word64 value.base) rfl
  exact different binding

theorem wrong_count_rejected (compiler : Compiler) (registers : Register → Word)
    (flags count : Word) (different : count ≠ 3) :
    ¬ResourcePre Grading.ByteScan.spec (ByteScanWindows.bytes compiler) (resources compiler)
      { machine compiler registers flags with registers := fun register =>
          if register = .rsi then count else (machine compiler registers flags).registers register } := by
  intro admitted
  have binding := admitted.arguments ⟨1, by decide⟩ (.word64 3) rfl
  exact different binding

/-- Swapping only the declared snapshot leaves real current bytes unchanged,
so the BufferAt admission rejects it despite an otherwise valid loan/world. -/
theorem wrong_snapshot_rejected (compiler : Compiler) :
    ¬ResourceContract (spec := Grading.ByteScan.spec)
      { resources compiler with value := ⟨value.base, [0x41, 0x43, 0]⟩ }
      (resources compiler).shared := by
  intro admitted
  have changed := admitted.buffers ⟨value.base, [0x41, 0x43, 0]⟩ (by simp [Grading.ByteScan.spec])
  have real := (buffer_snapshot compiler).2 1 0x42 rfl
  have wrong := changed.2 1 0x43 rfl
  have impossible : (0x42 : Byte) = 0x43 := Except.ok.inj (real.symm.trans wrong)
  exact (by decide +kernel : (0x42 : Byte) ≠ 0x43) impossible

/-- Live code authority cannot be substituted for the exact buffer loan. -/
theorem wrong_loan_rejected (compiler : Compiler) :
    ¬ResourceContract { resources compiler with inputLoan := fun _ => (resources compiler).call.codeLoan }
      (resources compiler).shared := by
  intro admitted
  obtain ⟨loan, live, _, region⟩ := admitted.inputs buffer (by simp [Grading.ByteScan.spec, resources, buffer])
    (by decide +kernel)
  obtain ⟨code, codeLive, _, codeRegion⟩ := code_held compiler
  have same : loan = code := Option.some.inj (live.symm.trans codeLive)
  have regions := region.symm.trans (same ▸ codeRegion)
  have bases := congrArg Region.base regions
  have different : buffer.base ≠ entry compiler := by cases compiler <;> decide +kernel
  exact different bases

/-- The useful last byte is backed by actual current authorization and a
successful DATA1 read, including the initialized zero byte. -/
theorem final_byte_authorized (compiler : Compiler) :
    ∃ identifier loan,
      Borrowing.authorize (resources compiler).shared (Threads.principal layout.worker) identifier = .ok loan ∧
      loan.region.Contains (value.base + 2) ∧
      readDataByte (toMemory (resources compiler).shared.resources.space) (value.base + 2) = .ok 0 := by
  have footprint : DataRead (Grading.ByteScan.spec.buffers value) ⟨.data, value.base + 2, 1⟩ := by
    refine ⟨rfl, buffer, by simp [Grading.ByteScan.spec, buffer], ?_⟩
    unfold Buffer.Contains
    decide +kernel
  obtain ⟨identifier, loan, _, authorized, inside, _, _⟩ :=
    (contract compiler).dataRead_bytes footprint (offset := 0) (by decide)
  refine ⟨identifier, loan, authorized, ?_, ?_⟩
  · simpa using inside
  · exact (buffer_snapshot compiler).2 2 0 rfl

/-- Padded allocation bytes remain readable, but count3 gives no DATA1
permission beyond its exact span; allocation size must not widen the loan. -/
theorem padding_denied (compiler : Compiler) :
    readDataByte (toMemory (resources compiler).shared.resources.space) (value.base + 3) = .ok 0 ∧
    ¬ReadAllowed (resources compiler) ⟨.data, value.base + 3, 1⟩ := by
  refine ⟨?_, ?_⟩
  · rw [space]
    rfl
  · intro allowed
    rcases allowed with stack | data
    · cases stack.1
    · obtain ⟨_, supplied, member, span⟩ := data.1
      have same : supplied = buffer := by simpa [Grading.ByteScan.spec, resources, buffer] using member
      subst supplied
      have outside : ¬buffer.Contains (value.base + 3) 1 := by
        unfold Buffer.Contains
        decide +kernel
      exact outside span

def ended (compiler : Compiler) : Borrowing.State :=
  { (resources compiler).shared with loans := fun query =>
      if query = (resources compiler).inputLoan buffer then none else (resources compiler).shared.loans query }

/-- Actual finishLoan revokes present authority without changing any RAM;
the old snapshot and initial well-formedness cannot resurrect that loan. -/
theorem revoked_rejected (compiler : Compiler) :
    Borrowing.finishLoan (resources compiler).shared (Threads.principal layout.worker)
      ((resources compiler).inputLoan buffer) = .ok (ended compiler) ∧
    (ended compiler).resources.space = (resources compiler).shared.resources.space ∧
    ¬ResourceContract (resources compiler) (ended compiler) := by
  obtain ⟨loan, live, borrower, _⟩ := buffer_held compiler
  refine ⟨?_, rfl, ?_⟩
  · simp [Borrowing.finishLoan, Borrowing.authorize, live, borrower, ended]
  · intro admitted
    obtain ⟨_, live, _, _⟩ := admitted.inputs buffer
      (by simp [Grading.ByteScan.spec, resources, buffer]) (by decide +kernel)
    simp [ended] at live

/-- Caller protection is real manager state: even its original owner cannot
write the live private return slot while its original loan is retained. -/
theorem caller_store_denied (compiler : Compiler) :
    Borrowing.mutate (resources compiler).shared
      (.store64 layout.callerOwner ⟨1, 0⟩ layout.stack 0) = .error .borrowed := by
  cases compiler <;> buffer_resource_kernel_rfl

/-- Exercise packing across a qword boundary, unaligned and above 4GiB.
Expected little-endian words and ninth byte are specified independently. -/
def wideSetup := Corpus.BufferResources.dataByteBuffer (Corpus.BufferResources.seed empty) 7 11
  ⟨0x100000001, [0x80, 0xff, 0, 1, 2, 3, 4, 5, 0x55]⟩

theorem wideSetup_total : wideSetup.toOption.isSome = true := by buffer_resource_kernel_rfl
def wide := wideSetup.toOption.get wideSetup_total

theorem packed_actual_reads :
    loadDWord (toMemory wide.1.shared.resources.space) 0x100000001 = .ok 0x0100ff80 ∧
    loadDWord (toMemory wide.1.shared.resources.space) 0x100000006 = .ok 0x55050403 ∧
    readDataByte (toMemory wide.1.shared.resources.space) 0x100000009 = .ok 0x55 ∧
    Borrowing.loadWord wide.1.shared (Threads.principal 11) wide.2 0x100000008 = .error .outsideLoan := by
  exact ⟨by buffer_resource_kernel_rfl, by buffer_resource_kernel_rfl,
    by buffer_resource_kernel_rfl, by buffer_resource_kernel_rfl⟩

#print axioms Windows.wrong_name_rejected
#print axioms Windows.shifted_rejected
#print axioms Windows.changed_last_rejected
#print axioms Windows.body_is_not_file
#print axioms Windows.header_tamper_rejected
#print axioms retained_header
#print axioms wrong_entry_rejected
#print axioms wrong_pointer_rejected
#print axioms wrong_count_rejected
#print axioms wrong_snapshot_rejected
#print axioms wrong_loan_rejected
#print axioms final_byte_authorized
#print axioms padding_denied
#print axioms revoked_rejected
#print axioms caller_store_denied
#print axioms packed_actual_reads
end EDSL.Tests.CorpusByteScanResources
#audit_edsl
