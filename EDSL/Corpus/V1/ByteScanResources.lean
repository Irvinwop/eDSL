/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.ByteScanWindows
import EDSL.Corpus.BufferResources
import EDSL.Grading.ByteScan

set_option autoImplicit false
set_option warningAsError true

/-! Useful current resources at each exact frozen entry, independent of any
instruction decoder or candidate behavior. The complete installed ELF survives
checked manager setup. This constructs one useful input, not every input of the
unrestricted mathematical contract, and grants no corpus/registry credit. -/

namespace EDSL.Corpus.V1.ByteScanResources
open X86 OS OS.AddressSpace BufferCall

abbrev Compiler := ByteScanWindows.Compiler

def entry (compiler : Compiler) : Word := (ByteScanWindows.function compiler).window.base
def installed (compiler : Compiler) : ELF.Loaded :=
  BufferResources.installed (ByteScanWindows.file compiler) (ByteScanWindows.input compiler)

theorem admitted (compiler : Compiler) :
    (ByteScanWindows.input compiler).admit (ByteScanWindows.file compiler)
      ByteScanWindows.name empty = .ok (installed compiler) :=
  BufferResources.admitted (ByteScanWindows.checked compiler)

theorem executable_permissions (compiler : Compiler) :
    ∀ segment ∈ (ByteScanWindows.input compiler).table.image.segments,
      segment.permissions.executable = true → segment.permissions = readExecute := by
  cases compiler <;> decide +kernel

def programSpace (compiler : Compiler) : Space :=
  BufferResources.programSpace (ByteScanWindows.file compiler) (ByteScanWindows.input compiler)

theorem programSpace_eq (compiler : Compiler) : programSpace compiler = (installed compiler).space :=
  BufferResources.programSpace_eq (ByteScanWindows.checked compiler) (executable_permissions compiler)

def layout : BufferResources.Layout := ⟨23, 21, 7, 11, 0x700008, 0x654320⟩
def values : List Byte := [0x41, 0x42, 0]
def value : Grading.ByteScan.Input := ⟨0x10000, values⟩
def buffer : Buffer := ⟨value.base, value.values⟩

def setup (compiler : Compiler) : Except Borrowing.Fault BufferResources.Ready :=
  BufferResources.setup (programSpace compiler) (entry compiler) (ByteScanWindows.bytes compiler)
    layout buffer

theorem setup_total (compiler : Compiler) : (setup compiler).toOption.isSome = true := by
  cases compiler <;> buffer_resource_kernel_rfl

def ready (compiler : Compiler) : BufferResources.Ready :=
  (setup compiler).toOption.get (setup_total compiler)

def resources (compiler : Compiler) : Resources Grading.ByteScan.spec :=
  ⟨(ready compiler).managed.shared,
    ⟨layout.worker, entry compiler, layout.stack, layout.returnAddress, ByteScanWindows.bytes compiler,
      (ready compiler).codeLoan, (ready compiler).callerLoan⟩,
    value, fun _ => (ready compiler).inputLoan⟩

/-- Normalization projection, proved equal to the actual checked result below. -/
def spaceView (compiler : Compiler) : Space :=
  BufferResources.freshQWord
    (BufferResources.freshQWord (programSpace compiler) layout.stack layout.returnAddress)
    value.base 0x4241

theorem space (compiler : Compiler) :
    (resources compiler).shared.resources.space = spaceView compiler := by
  cases compiler <;> buffer_resource_kernel_rfl

theorem installed_free (compiler : Compiler) (address : Word)
    (selected : address = value.base ∨ address = layout.stack) :
    allUnmapped (installed compiler).space ⟨address, 8⟩ = true := by
  rcases selected with rfl | rfl <;> cases compiler <;> decide +kernel

/-- EVERY installed cell, including noncode segments, metadata and permissions,
is retained. Allocation/store/protection touch only previously unmapped cells. -/
theorem installed_frame (compiler : Compiler) {address : Word} {original : AddressSpace.Cell}
    (existing : (installed compiler).space.cells address = some original) :
    (resources compiler).shared.resources.space.cells address = some original := by
  have outside (base : Word) (selected : base = value.base ∨ base = layout.stack) :
      ¬ (⟨base, 8⟩ : Region).Contains address := by
    intro inside
    have absent := allUnmapped_inside _ _ (installed_free compiler base selected) address inside
    rw [existing] at absent
    cases absent
  rw [space]
  unfold spaceView
  rw [BufferResources.freshQWord_frame _ _ _ _ (outside value.base (Or.inl rfl)),
    BufferResources.freshQWord_frame _ _ _ _ (outside layout.stack (Or.inr rfl)), programSpace_eq]
  exact existing

theorem text (compiler : Compiler) :
    ELF.FunctionWindow.TextUnchanged (toMemory (installed compiler).space)
      (toMemory (resources compiler).shared.resources.space)
      (ByteScanWindows.function compiler).window (ByteScanWindows.bytes compiler).length := by
  intro index bound
  have original := BufferResources.installed_cell (ByteScanWindows.checked compiler)
    (executable_permissions compiler) index bound
  have present := installed_frame compiler original
  change (installed compiler).space.cells
    ((ByteScanWindows.function compiler).window.base + BitVec.ofNat 64 index) =
      some ⟨(ByteScanWindows.bytes compiler)[index], readExecute⟩ at original
  change (resources compiler).shared.resources.space.cells
    ((ByteScanWindows.function compiler).window.base + BitVec.ofNat 64 index) =
      some ⟨(ByteScanWindows.bytes compiler)[index], readExecute⟩ at present
  constructor <;> simp only [toMemory, present, original] <;> rfl

theorem current_code (compiler : Compiler) :
    CodeAt (toMemory (resources compiler).shared.resources.space) (entry compiler)
      (ByteScanWindows.bytes compiler) :=
  ELF.FunctionSymbol.admitted_current_code (admitted compiler) (text compiler)

theorem code_held (compiler : Compiler) :
    Threads.HasLoan (resources compiler).shared layout.worker (resources compiler).call.codeLoan
      ⟨entry compiler, (ByteScanWindows.bytes compiler).length⟩ := by
  refine ⟨⟨⟨0, 0⟩, layout.codeOwner, Threads.principal layout.worker,
    ⟨entry compiler, (ByteScanWindows.bytes compiler).length⟩⟩, ?_, rfl, rfl⟩
  cases compiler <;> buffer_resource_kernel_rfl

theorem caller_held (compiler : Compiler) :
    Threads.HasLoan (resources compiler).shared layout.worker (resources compiler).call.stackLoan
      ⟨layout.stack, 8⟩ := by
  refine ⟨⟨⟨1, 0⟩, layout.callerOwner, Threads.principal layout.worker, ⟨layout.stack, 8⟩⟩,
    ?_, rfl, rfl⟩
  cases compiler <;> buffer_resource_kernel_rfl

theorem buffer_held (compiler : Compiler) :
    Threads.HasLoan (resources compiler).shared layout.worker
      ((resources compiler).inputLoan buffer) buffer.region := by
  refine ⟨⟨⟨2, 0⟩, layout.dataOwner, Threads.principal layout.worker, buffer.region⟩, ?_, rfl, rfl⟩
  cases compiler <;> buffer_resource_kernel_rfl

theorem caller_read (compiler : Compiler) :
    readWord (toMemory (resources compiler).shared.resources.space) layout.stack =
      .ok layout.returnAddress := by
  rw [space]
  cases compiler <;> buffer_resource_kernel_rfl

theorem buffer_snapshot (compiler : Compiler) :
    BufferAt (toMemory (resources compiler).shared.resources.space) buffer.base buffer.bytes := by
  refine ⟨by decide +kernel, ?_⟩
  intro index byte present
  change values[index]? = some byte at present
  rw [space]
  match index with
  | 0 | 1 | 2 => simp [values] at present; subst byte; rfl
  | index + 3 => simp [values] at present

theorem contract (compiler : Compiler) :
    ResourceContract (resources compiler) (resources compiler).shared := by
  refine ⟨⟨(ready compiler).managed.valid, code_held compiler, caller_held compiler,
    current_code compiler, caller_read compiler, ?_, ?_, ?_⟩, ?_, ?_⟩
  · change canonical layout.returnAddress = true
    decide +kernel
  · change layout.stack.toNat + 8 < 2^64
    decide +kernel
  · change canonical (layout.stack + 8) = true
    decide +kernel
  · intro supplied member
    have same : supplied = buffer := by simpa [Grading.ByteScan.spec, resources, buffer] using member
    subst supplied
    exact buffer_snapshot compiler
  · intro supplied member _
    have same : supplied = buffer := by simpa [Grading.ByteScan.spec, resources, buffer] using member
    subst supplied
    exact buffer_held compiler

/-- Registers other than RSP/RDI/RSI and the complete initial flags are retained.
No return value, execution, decoder, rank or candidate certificate enters Pre. -/
def machine (compiler : Compiler) (registers : Register → Word) (flags : Word) : X86.State where
  registers register := match register with
    | .rsp => layout.stack
    | .rdi => value.base
    | .rsi => BitVec.ofNat 64 value.values.length
    | other => registers other
  flags := flags
  rip := entry compiler
  memory := toMemory (resources compiler).shared.resources.space

theorem pre (compiler : Compiler) (registers : Register → Word) (flags : Word) :
    ResourcePre Grading.ByteScan.spec (ByteScanWindows.bytes compiler) (resources compiler)
      (machine compiler registers flags) := by
  refine ⟨⟨contract compiler, rfl⟩, rfl, rfl, rfl, ?_, ?_⟩
  · change values.length < 2^64
    decide +kernel
  ·
    intro index argument binding
    obtain ⟨index, bound⟩ := index
    match index with
    | 0 | 1 =>
      simp [Grading.ByteScan.spec, resources] at binding
      subst argument
      rfl
    | index + 2 => simp [Grading.ByteScan.spec, resources] at binding

theorem raw_pre (compiler : Compiler) (registers : Register → Word) (flags : Word) :
    Pre Grading.ByteScan.spec (ByteScanWindows.bytes compiler) (resourceInput (resources compiler))
      (machine compiler registers flags) := (pre compiler registers flags).machine

theorem useful : Grading.ByteScan.spec.useful value := by
  change values ≠ []
  decide +kernel

/-- Useful raw and resource witnesses for the exact unchanged BufferCall task;
this is present-domain evidence, not a semantic claim or typed registration. -/
theorem nonvacuous (compiler : Compiler) :
    Grading.ReadOnlyNonvacuous (readOnlyTask Grading.ByteScan.spec) (ByteScanWindows.bytes compiler) :=
  nonvacuous_of_resource (resources compiler) (machine compiler (fun _ => 0) 0x202)
    useful (pre compiler (fun _ => 0) 0x202)

/-- The original return slot is privately owned, canonical and SysV aligned;
the chosen useful entry has DF clear. -/
theorem caller_abi (compiler : Compiler) (registers : Register → Word) :
    ((machine compiler registers 0x202).registers .rsp).toNat % 16 = 8 ∧
    canonical ((machine compiler registers 0x202).registers .rsp) = true ∧
    (machine compiler registers 0x202).flags.getLsbD 10 = false ∧
    Ownership.authorize (resources compiler).shared.resources layout.callerOwner ⟨1, 0⟩ =
      .ok ⟨layout.callerOwner, 0, ⟨layout.stack, 8⟩⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change layout.stack.toNat % 16 = 8
    decide +kernel
  · change canonical layout.stack = true
    decide +kernel
  · change (0x202 : Word).getLsbD 10 = false
    decide +kernel
  · cases compiler <;> buffer_resource_kernel_rfl

/-- Package all file/runtime obligations for root's later typed registry step. -/
structure Witness (compiler : Compiler) where
  resource : Resources Grading.ByteScan.spec
  initial : X86.State
  useful : Grading.ByteScan.spec.useful resource.value
  pre : ResourcePre Grading.ByteScan.spec (ByteScanWindows.bytes compiler) resource initial
  entry : initial.rip = (ByteScanWindows.function compiler).window.base
  text : ELF.FunctionWindow.TextUnchanged (toMemory (installed compiler).space) initial.memory
    (ByteScanWindows.function compiler).window (ByteScanWindows.bytes compiler).length
  retained : ∀ address cell, (installed compiler).space.cells address = some cell →
    resource.shared.resources.space.cells address = some cell

def witness (compiler : Compiler) (registers : Register → Word) (flags : Word) : Witness compiler :=
  ⟨resources compiler, machine compiler registers flags, useful, pre compiler registers flags,
    rfl, text compiler, fun _ _ existing => installed_frame compiler existing⟩

#print axioms admitted
#print axioms programSpace_eq
#print axioms setup_total
#print axioms installed_frame
#print axioms contract
#print axioms pre
#print axioms nonvacuous
#print axioms witness
end EDSL.Corpus.V1.ByteScanResources
#audit_edsl
