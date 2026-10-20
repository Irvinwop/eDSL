/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.IndexSearchResources

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.CorpusIndexSearchResources
open X86 OS OS.AddressSpace BufferCall Corpus.V1 IndexSearchResources

def other : Operation → Operation | .byte => .u32 | .u32 => .byte

/-- Both names are authentic symbols in the SAME file. Selecting a valid row
for the wrong requested name must still fail. -/
theorem wrong_name_rejected (compiler : Compiler) (operation : Operation) :
    (IndexSearchWindows.input compiler operation).check (IndexSearchWindows.file compiler)
      (IndexSearchWindows.name (other operation)) = false := by
  cases accepted : (IndexSearchWindows.input compiler operation).check (IndexSearchWindows.file compiler)
      (IndexSearchWindows.name (other operation)) with
  | false => rfl
  | true =>
    have wrong := (ELF.FunctionSymbol.checked_sound accepted).2.1.2.2.1
    have right := (ELF.FunctionSymbol.checked_sound
      (IndexSearchWindows.checked compiler (other operation))).2.1.2.2.1
    change (IndexSearchWindows.input compiler operation).metadata.matches
      (IndexSearchWindows.name (other operation)) =
        [(IndexSearchWindows.function compiler (other operation)).occurrence] at right
    have same := List.singleton_inj.mp (right.symm.trans wrong)
    have index := congrArg ELF.FunctionSymbol.Occurrence.index same
    have different : (IndexSearchWindows.function compiler (other operation)).occurrence.index ≠
        (IndexSearchWindows.function compiler operation).occurrence.index := by
      cases compiler <;> cases operation <;> decide +kernel
    exact False.elim (different index)

def shifted (compiler : Compiler) (operation : Operation) : Corpus.FunctionInput :=
  { IndexSearchWindows.input compiler operation with function :=
    { IndexSearchWindows.function compiler operation with window :=
      { (IndexSearchWindows.function compiler operation).window with address :=
        (IndexSearchWindows.function compiler operation).window.address + 1 } } }

/-- Even correct file bytes and the real name cannot excuse a displaced entry. -/
theorem shifted_rejected (compiler : Compiler) (operation : Operation) :
    (shifted compiler operation).check (IndexSearchWindows.file compiler)
      (IndexSearchWindows.name operation) = false := by
  cases accepted : (shifted compiler operation).check (IndexSearchWindows.file compiler)
      (IndexSearchWindows.name operation) with
  | false => rfl
  | true =>
    have address := (ELF.FunctionSymbol.checked_mapping accepted).1
    change (IndexSearchWindows.function compiler operation).occurrence.symbol.value + 1 =
      (IndexSearchWindows.function compiler operation).occurrence.symbol.value at address
    omega

/-- The LAST writable BSS cell is far outside the code and ELF header. This
detects text-only worlds, dropped zero-fill tails, or blanket RX protection. -/
theorem retained_bss (compiler : Compiler) (operation : Operation) :
    readDataByte (witness compiler operation).initial.memory 0x40910f = .ok 0 ∧
      (witness compiler operation).initial.memory.writable 0x40910f = true ∧
      (witness compiler operation).initial.memory.executable 0x40910f = false := by
  have original : (installed compiler operation).space.cells 0x40910f = some ⟨0, readWrite⟩ := by
    rw [installed_seed]
    cases compiler <;> buffer_resource_kernel_rfl
  have present := installed_frame compiler operation original
  change readDataByte (toMemory (resources compiler operation).shared.resources.space) 0x40910f = _ ∧
    (toMemory (resources compiler operation).shared.resources.space).writable 0x40910f = _ ∧
    (toMemory (resources compiler operation).shared.resources.space).executable 0x40910f = _
  refine ⟨?_, ?_, ?_⟩ <;> simp only [readDataByte, toMemory, present] <;> buffer_resource_kernel_rfl

theorem wrong_entry_rejected (compiler : Compiler) (operation : Operation) :
    ¬ ResourcePre (spec operation) (IndexSearchWindows.bytes compiler operation)
      (resources compiler operation)
      { (witness compiler operation).initial with rip := entry compiler operation + 1 } := by
  intro admitted
  have address := admitted.entry
  have different : entry compiler operation + 1 ≠ entry compiler operation := by
    cases compiler <;> cases operation <;> decide +kernel
  exact different address

theorem wrong_pointer_rejected (compiler : Compiler) (operation : Operation) (pointer : Word)
    (different : pointer ≠ (buffer operation).base) :
    ¬ ResourcePre (spec operation) (IndexSearchWindows.bytes compiler operation)
      (resources compiler operation)
      { (witness compiler operation).initial with registers := fun register =>
        if register = .rdi then pointer else (witness compiler operation).initial.registers register } := by
  intro admitted
  have binding := admitted.arguments ⟨0, by decide⟩ (.word64 (buffer operation).base)
    (by cases operation <;> rfl)
  exact different binding

theorem wrong_count_rejected (compiler : Compiler) (operation : Operation) (length : Word)
    (different : length ≠ BitVec.ofNat 64 (count operation)) :
    ¬ ResourcePre (spec operation) (IndexSearchWindows.bytes compiler operation)
      (resources compiler operation)
      { (witness compiler operation).initial with registers := fun register =>
        if register = .rsi then length else (witness compiler operation).initial.registers register } := by
  intro admitted
  have binding := admitted.arguments ⟨1, by decide⟩ (.word64 (BitVec.ofNat 64 (count operation)))
    (by cases operation <;> rfl)
  exact different binding

/-- The registered key binding must reject changed low bits, while leaving
the upper 56/32 bits unrestricted. -/
theorem wrong_key_rejected (compiler : Compiler) (operation : Operation) (key : Word)
    (different : ¬ KeyBound operation key) :
    ¬ ResourcePre (spec operation) (IndexSearchWindows.bytes compiler operation)
      (resources compiler operation) (machine compiler operation (fun _ => 0) 0x202 key) := by
  intro admitted
  cases operation with
  | byte =>
    have binding := admitted.arguments ⟨2, by decide⟩ (.low8 0) rfl
    exact different binding
  | u32 =>
    have binding := admitted.arguments ⟨2, by decide⟩ (.low32 0) rfl
    exact different binding

theorem upper_key_bits_accepted (compiler : Compiler) :
    ResourcePre (spec .byte) (IndexSearchWindows.bytes compiler .byte) (resources compiler .byte)
      (machine compiler .byte (fun _ => 0) 0x202 0xdeadbeef12345600) ∧
    ResourcePre (spec .u32) (IndexSearchWindows.bytes compiler .u32) (resources compiler .u32)
      (machine compiler .u32 (fun _ => 0) 0x202 0xdeadbeef00000000) := by
  exact ⟨pre compiler .byte _ _ _ (by change (0xdeadbeef12345600 : Word).setWidth 8 = 0; decide +kernel),
    pre compiler .u32 _ _ _ (by change (0xdeadbeef00000000 : Word).setWidth 32 = 0; decide +kernel)⟩

/-- Changing the second mathematical word without storing it must fail even
with a valid full eight-byte loan and otherwise unchanged resources. -/
theorem wrong_snapshot_rejected (compiler : Compiler) :
    ¬ ResourceContract (spec := spec .u32)
      { resources compiler .u32 with value := ⟨0x10000, [0x4241, 1], 0⟩ }
      (resources compiler .u32).shared := by
  intro admitted
  have changed := admitted.buffers
    (Grading.IndexSearch.u32Buffer ⟨0x10000, [0x4241, 1], 0⟩) (by simp [spec,
      taskID, Grading.BufferTask.registeredSpec, Grading.IndexSearch.u32Spec])
  have real := (buffer_snapshot compiler .u32).2 4 0 rfl
  have wrong := changed.2 4 1 rfl
  have impossible : (0 : Byte) = 1 := Except.ok.inj (real.symm.trans wrong)
  exact (by decide +kernel : (0 : Byte) ≠ 1) impossible

/-- A compatible old three-byte loan is not authority for the new eight-byte
word buffer. This catches accidental reuse/reinterpretation of the seed ID. -/
theorem old_short_loan_rejected (compiler : Compiler) :
    ¬ ResourceContract
      { resources compiler .u32 with inputLoan := fun _ =>
          (ByteScanResources.resources compiler).inputLoan ByteScanResources.buffer }
      (resources compiler .u32).shared := by
  intro admitted
  obtain ⟨loan, live, _, region⟩ := admitted.inputs (buffer .u32)
    (by simp [spec, taskID, Grading.BufferTask.registeredSpec, Grading.IndexSearch.u32Spec,
      resources, buffer]) (by decide +kernel)
  obtain ⟨old, oldLive, _, oldRegion⟩ := ByteScanResources.buffer_held compiler
  have retained := original_loans compiler .u32 oldLive
  have same : loan = old := Option.some.inj (live.symm.trans retained)
  have extents := congrArg Region.length (region.symm.trans (same ▸ oldRegion))
  change 8 = 3 at extents
  omega

/-- Actual DATA4 reads of BOTH words use the issued eight-byte loan. The last
word occupies bytes 4..7, beyond every byte of the seed's three-byte loan. -/
theorem both_words_authorized (compiler : Compiler) :
    (∃ first, Borrowing.loadWord (resources compiler .u32).shared (Threads.principal layout.worker)
        ((resources compiler .u32).inputLoan (buffer .u32)) 0x10000 = .ok first) ∧
    (∃ second, Borrowing.loadWord (resources compiler .u32).shared (Threads.principal layout.worker)
        ((resources compiler .u32).inputLoan (buffer .u32)) 0x10004 = .ok second) ∧
    Borrowing.loadWord (resources compiler .u32).shared (Threads.principal layout.worker)
        ((resources compiler .u32).inputLoan (buffer .u32)) 0x10005 = .error .outsideLoan := by
  refine ⟨⟨0x4241, ?_⟩, ⟨0, ?_⟩, ?_⟩ <;> cases compiler <;> buffer_resource_kernel_rfl

/-- Readable padding cannot widen the byte snapshot, and a partially contained
word cannot borrow its missing byte from the adjacent readable input. -/
theorem padding_and_crossing_denied (compiler : Compiler) :
    readDataByte (toMemory (resources compiler .byte).shared.resources.space) 0x10003 = .ok 0 ∧
    ¬ ReadAllowed (resources compiler .byte) ⟨.data, 0x10003, 1⟩ ∧
    ¬ ReadAllowed (resources compiler .u32) ⟨.data, 0x10005, 4⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [space, ByteScanResources.space]
    rfl
  · intro allowed
    rcases allowed with stack | data
    · cases stack.1
    · obtain ⟨_, supplied, member, span⟩ := data.1
      have same : supplied = buffer .byte := by
        simpa [spec, taskID, Grading.BufferTask.registeredSpec, Grading.IndexSearch.byteSpec,
          resources, buffer] using member
      subst supplied
      have outside : ¬ (buffer .byte).Contains 0x10003 1 := by
        unfold Buffer.Contains
        decide +kernel
      exact outside span
  · intro allowed
    rcases allowed with stack | data
    · cases stack.1
    · obtain ⟨_, supplied, member, span⟩ := data.1
      have same : supplied = buffer .u32 := by
        simpa [spec, taskID, Grading.BufferTask.registeredSpec, Grading.IndexSearch.u32Spec,
          resources, buffer] using member
      subst supplied
      have outside : ¬ (buffer .u32).Contains 0x10005 4 := by
        unfold Buffer.Contains
        decide +kernel
      exact outside span

def ended (compiler : Compiler) (operation : Operation) : Borrowing.State :=
  { (resources compiler operation).shared with loans := fun query =>
    if query = (resources compiler operation).inputLoan (buffer operation) then none
    else (resources compiler operation).shared.loans query }

/-- A real finishLoan action leaves all RAM unchanged but removes current
input authority; the remaining seed loan cannot resurrect the revoked ID. -/
theorem revoked_rejected (compiler : Compiler) (operation : Operation) :
    Borrowing.finishLoan (resources compiler operation).shared (Threads.principal layout.worker)
      ((resources compiler operation).inputLoan (buffer operation)) = .ok (ended compiler operation) ∧
    (ended compiler operation).resources.space = (resources compiler operation).shared.resources.space ∧
    ¬ ResourceContract (resources compiler operation) (ended compiler operation) := by
  obtain ⟨loan, live, borrower, _⟩ := buffer_held compiler operation
  refine ⟨?_, rfl, ?_⟩
  · simp [Borrowing.finishLoan, Borrowing.authorize, live, borrower, ended]
  · intro admitted
    obtain ⟨_, live, _, _⟩ := admitted.inputs (buffer operation)
      (by cases operation <;> simp [spec, taskID, Grading.BufferTask.registeredSpec,
        Grading.IndexSearch.byteSpec, Grading.IndexSearch.u32Spec, resources, buffer])
      (by cases operation <;> decide +kernel)
    simp [ended] at live

/-- The original private caller allocation is still frozen by its original
loan after extension. Even its owner cannot rewrite the return hook. -/
theorem caller_store_denied (compiler : Compiler) (operation : Operation) :
    Borrowing.mutate (resources compiler operation).shared
      (.store64 layout.callerOwner ⟨1, 0⟩ layout.stack 0) = .error .borrowed := by
  cases compiler <;> cases operation <;> buffer_resource_kernel_rfl

def emptyValue : (operation : Operation) → Word → (spec operation).Input
  | .byte, pointer => (⟨pointer, [], 0⟩ : Grading.IndexSearch.ByteInput)
  | .u32, pointer => (⟨pointer, [], 0⟩ : Grading.IndexSearch.U32Input)

/-- Arbitrary pointers (including noncanonical, unaligned values) and arbitrary
unused IDs need no input loan. The original caller/code resources still apply. -/
theorem empty_no_input_loan (compiler : Compiler) (operation : Operation) (pointer : Word)
    (unused : Nat) :
    ResourceContract
      { resources compiler operation with
        value := emptyValue operation pointer
        inputLoan := fun _ => unused } (resources compiler operation).shared := by
  apply ResourceContract.of_empty (resource :=
    { resources compiler operation with
      value := emptyValue operation pointer
      inputLoan := fun _ => unused }) (contract compiler operation).call
  intro supplied member
  cases operation <;> simp [spec, taskID, Grading.BufferTask.registeredSpec,
    Grading.IndexSearch.byteSpec, Grading.IndexSearch.u32Spec, emptyValue] at member <;>
    subst supplied <;> rfl

#print axioms wrong_name_rejected
#print axioms shifted_rejected
#print axioms retained_bss
#print axioms wrong_entry_rejected
#print axioms wrong_pointer_rejected
#print axioms wrong_count_rejected
#print axioms wrong_key_rejected
#print axioms upper_key_bits_accepted
#print axioms wrong_snapshot_rejected
#print axioms old_short_loan_rejected
#print axioms both_words_authorized
#print axioms padding_and_crossing_denied
#print axioms revoked_rejected
#print axioms caller_store_denied
#print axioms empty_no_input_loan
end EDSL.Tests.CorpusIndexSearchResources
#audit_edsl
