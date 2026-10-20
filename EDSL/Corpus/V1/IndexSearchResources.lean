/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.ReadOnlyResources
import EDSL.Corpus.V1.ByteScanResources
import EDSL.Corpus.V1.IndexSearchWindows
import EDSL.Grading.BufferTask

set_option autoImplicit false
set_option warningAsError true

/-! Useful current calls for the four authenticated search windows. Only the
existing byte-scan initialization is reused: no body or certificate is imported.
The fixed registered tasks remain unrestricted universal obligations elsewhere.
Every installed cell and the original caller loan inhabit this same manager. -/

namespace EDSL.Corpus.V1.IndexSearchResources
open X86 OS OS.AddressSpace BufferCall

abbrev Compiler := IndexSearchWindows.Compiler
abbrev Operation := IndexSearchWindows.Operation
abbrev layout := ByteScanResources.layout

def taskID : Operation → Grading.BufferTask.TaskID
  | .byte => .memchrIndex
  | .u32 => .linearSearchU32

def spec (operation : Operation) : Spec := Grading.BufferTask.registeredSpec (taskID operation)

def entry (compiler : Compiler) (operation : Operation) : Word :=
  (IndexSearchWindows.function compiler operation).window.base

def installed (compiler : Compiler) (operation : Operation) : ELF.Loaded :=
  BufferResources.installed (IndexSearchWindows.file compiler) (IndexSearchWindows.input compiler operation)

theorem admitted (compiler : Compiler) (operation : Operation) :
    (IndexSearchWindows.input compiler operation).admit (IndexSearchWindows.file compiler)
      (IndexSearchWindows.name operation) empty = .ok (installed compiler operation) :=
  BufferResources.admitted (IndexSearchWindows.checked compiler operation)

theorem installed_seed (compiler : Compiler) (operation : Operation) :
    installed compiler operation = ByteScanResources.installed compiler := rfl

theorem executable_permissions (compiler : Compiler) (operation : Operation) :
    ∀ segment ∈ (IndexSearchWindows.input compiler operation).table.image.segments,
      segment.permissions.executable = true → segment.permissions = readExecute :=
  ByteScanResources.executable_permissions compiler

def value : (operation : Operation) → (spec operation).Input
  | .byte => (⟨0x10000, [0x41, 0x42, 0], 0⟩ : Grading.IndexSearch.ByteInput)
  | .u32 => (⟨0x10000, [0x4241, 0], 0⟩ : Grading.IndexSearch.U32Input)

def buffer : Operation → Buffer
  | .byte => Grading.IndexSearch.byteBuffer (value .byte)
  | .u32 => Grading.IndexSearch.u32Buffer (value .u32)

/-- Normalization view only: the complete image and the two initialized qwords
are unchanged. The new authenticated code slice has a faster byte index. -/
def spaceView (compiler : Compiler) (operation : Operation) : Space :=
  BufferResources.freshQWord
    (BufferResources.freshQWord
      (BufferResources.programSpace (IndexSearchWindows.file compiler)
        (IndexSearchWindows.input compiler operation)) layout.stack layout.returnAddress)
    0x10000 0x4241

theorem spaceView_eq (compiler : Compiler) (operation : Operation) :
    spaceView compiler operation = (ByteScanResources.resources compiler).shared.resources.space := by
  rw [ByteScanResources.space]
  unfold spaceView ByteScanResources.spaceView
  rw [BufferResources.programSpace_eq (IndexSearchWindows.checked compiler operation)
    (executable_permissions compiler operation), ByteScanResources.programSpace_eq]
  rfl

def seed (compiler : Compiler) (operation : Operation) : BufferResources.Managed :=
  ReadOnlyResources.reindex (ByteScanResources.ready compiler).managed
    (spaceView compiler operation) (spaceView_eq compiler operation)

theorem seed_shared (compiler : Compiler) (operation : Operation) :
    (seed compiler operation).shared = (ByteScanResources.resources compiler).shared :=
  ReadOnlyResources.reindex_shared _ _ _

/-- The old three-byte read loan remains live and compatible. The second
borrow issues a NEW exact eight-byte loan for the u32 snapshot. -/
def setup (compiler : Compiler) (operation : Operation) :
    Except Borrowing.Fault (ReadOnlyResources.Attached (seed compiler operation) layout.worker
      ⟨entry compiler operation, (IndexSearchWindows.bytes compiler operation).length⟩ (buffer operation)) :=
  ReadOnlyResources.attach (seed compiler operation) layout.codeOwner layout.dataOwner ⟨2, 0⟩ layout.worker
    ⟨entry compiler operation, (IndexSearchWindows.bytes compiler operation).length⟩ (buffer operation)

theorem setup_total (compiler : Compiler) (operation : Operation) :
    (setup compiler operation).toOption.isSome = true := by
  cases compiler <;> cases operation <;> buffer_resource_kernel_rfl

def ready (compiler : Compiler) (operation : Operation) :=
  (setup compiler operation).toOption.get (setup_total compiler operation)

def resources (compiler : Compiler) (operation : Operation) : Resources (spec operation) :=
  ⟨(ready compiler operation).managed.shared,
    ⟨layout.worker, entry compiler operation, layout.stack, layout.returnAddress,
      IndexSearchWindows.bytes compiler operation, (ready compiler operation).codeLoan,
      (ByteScanResources.ready compiler).callerLoan⟩,
    value operation, fun _ => (ready compiler operation).inputLoan⟩

theorem space (compiler : Compiler) (operation : Operation) :
    (resources compiler operation).shared.resources.space =
      (ByteScanResources.resources compiler).shared.resources.space :=
  (ready compiler operation).space.trans
    (congrArg (fun shared : Borrowing.State => shared.resources.space) (seed_shared compiler operation))

theorem checked_history (compiler : Compiler) (operation : Operation) :
    Borrowing.History (ByteScanResources.resources compiler).shared
      (resources compiler operation).shared := by
  rw [← seed_shared compiler operation]
  exact (ready compiler operation).history

theorem original_loans (compiler : Compiler) (operation : Operation)
    {identifier : Nat} {loan : Borrowing.Loan}
    (live : (ByteScanResources.resources compiler).shared.loans identifier = some loan) :
    (resources compiler operation).shared.loans identifier = some loan :=
  (ready compiler operation).loans _ _ (by simpa only [seed_shared] using live)

/-- ALL installed ELF cells, including data/metadata and every permission bit,
survive the checked bootstrap and this adoption/borrowing extension. -/
theorem installed_frame (compiler : Compiler) (operation : Operation)
    {address : Word} {original : AddressSpace.Cell}
    (existing : (installed compiler operation).space.cells address = some original) :
    (resources compiler operation).shared.resources.space.cells address = some original := by
  rw [space]
  exact ByteScanResources.installed_frame compiler (by simpa only [installed_seed] using existing)

theorem text (compiler : Compiler) (operation : Operation) :
    ELF.FunctionWindow.TextUnchanged (toMemory (installed compiler operation).space)
      (toMemory (resources compiler operation).shared.resources.space)
      (IndexSearchWindows.function compiler operation).window
      (IndexSearchWindows.bytes compiler operation).length := by
  intro index bound
  have original := BufferResources.installed_cell (IndexSearchWindows.checked compiler operation)
    (executable_permissions compiler operation) index bound
  have present := installed_frame compiler operation original
  change (installed compiler operation).space.cells
    ((IndexSearchWindows.function compiler operation).window.base + BitVec.ofNat 64 index) =
      some ⟨(IndexSearchWindows.bytes compiler operation)[index], readExecute⟩ at original
  change (resources compiler operation).shared.resources.space.cells
    ((IndexSearchWindows.function compiler operation).window.base + BitVec.ofNat 64 index) =
      some ⟨(IndexSearchWindows.bytes compiler operation)[index], readExecute⟩ at present
  constructor <;> simp only [toMemory, present, original] <;> rfl

theorem current_code (compiler : Compiler) (operation : Operation) :
    CodeAt (toMemory (resources compiler operation).shared.resources.space) (entry compiler operation)
      (IndexSearchWindows.bytes compiler operation) :=
  ELF.FunctionSymbol.admitted_current_code (admitted compiler operation) (text compiler operation)

theorem code_held (compiler : Compiler) (operation : Operation) :
    Threads.HasLoan (resources compiler operation).shared layout.worker
      (resources compiler operation).call.codeLoan
      ⟨entry compiler operation, (IndexSearchWindows.bytes compiler operation).length⟩ :=
  (ready compiler operation).codeHeld

theorem caller_held (compiler : Compiler) (operation : Operation) :
    Threads.HasLoan (resources compiler operation).shared layout.worker
      (resources compiler operation).call.stackLoan ⟨layout.stack, 8⟩ :=
  (ready compiler operation).original_loan
    (by
      change Threads.HasLoan (seed compiler operation).shared layout.worker
        (ByteScanResources.ready compiler).callerLoan ⟨layout.stack, 8⟩
      rw [seed_shared]
      exact ByteScanResources.caller_held compiler)

theorem caller_private (compiler : Compiler) (operation : Operation) :
    Ownership.authorize (resources compiler operation).shared.resources layout.callerOwner ⟨1, 0⟩ =
      .ok ⟨layout.callerOwner, 0, ⟨layout.stack, 8⟩⟩ :=
  (ready compiler operation).authorize
    (by simpa only [seed_shared] using (ByteScanResources.caller_abi compiler (fun _ => 0)).2.2.2)

theorem buffer_held (compiler : Compiler) (operation : Operation) :
    Threads.HasLoan (resources compiler operation).shared layout.worker
      ((resources compiler operation).inputLoan (buffer operation)) (buffer operation).region :=
  (ready compiler operation).inputHeld (by cases operation <;> decide +kernel)

theorem caller_read (compiler : Compiler) (operation : Operation) :
    readWord (toMemory (resources compiler operation).shared.resources.space) layout.stack =
      .ok layout.returnAddress := by
  rw [space]
  exact ByteScanResources.caller_read compiler

theorem buffer_snapshot (compiler : Compiler) (operation : Operation) :
    BufferAt (toMemory (resources compiler operation).shared.resources.space)
      (buffer operation).base (buffer operation).bytes := by
  rw [space, ByteScanResources.space]
  refine ⟨by cases operation <;> decide +kernel, ?_⟩
  intro index byte present
  cases operation with
  | byte =>
    match index with
    | 0 | 1 | 2 => simp [buffer, value, Grading.IndexSearch.byteBuffer] at present; subst byte; rfl
    | index + 3 => simp [buffer, value, Grading.IndexSearch.byteBuffer] at present
  | u32 =>
    match index with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 =>
      simp [buffer, value, Grading.IndexSearch.u32Buffer, Elements.u32Bytes, Elements.dwordBytes] at present
      subst byte
      rfl
    | index + 8 =>
      simp [buffer, value, Grading.IndexSearch.u32Buffer, Elements.u32Bytes, Elements.dwordBytes] at present

theorem contract (compiler : Compiler) (operation : Operation) :
    ResourceContract (resources compiler operation) (resources compiler operation).shared := by
  refine ⟨⟨(ready compiler operation).managed.valid, code_held compiler operation,
    caller_held compiler operation, current_code compiler operation, caller_read compiler operation,
    ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact (ByteScanResources.contract compiler).call.returnCanonical
  · exact (ByteScanResources.contract compiler).call.stackBound
  · exact (ByteScanResources.contract compiler).call.postStackCanonical
  · intro supplied member
    have same : supplied = buffer operation := by
      cases operation <;> simpa [resources, spec, taskID, Grading.BufferTask.registeredSpec,
        Grading.IndexSearch.byteSpec, Grading.IndexSearch.u32Spec, buffer] using member
    subst supplied
    exact buffer_snapshot compiler operation
  · intro supplied member _
    have same : supplied = buffer operation := by
      cases operation <;> simpa [resources, spec, taskID, Grading.BufferTask.registeredSpec,
        Grading.IndexSearch.byteSpec, Grading.IndexSearch.u32Spec, buffer] using member
    subst supplied
    exact buffer_held compiler operation

/-- Only the specified low key bits are constrained; all upper bits and the
other registers/flags remain arbitrary in ResourcePre. -/
def KeyBound : Operation → Word → Prop
  | .byte, key => key.setWidth 8 = 0
  | .u32, key => key.setWidth 32 = 0

def count : Operation → Nat | .byte => 3 | .u32 => 2

def machine (compiler : Compiler) (operation : Operation) (registers : Register → Word)
    (flags key : Word) : X86.State where
  registers register := match register with
    | .rsp => layout.stack
    | .rdi => (buffer operation).base
    | .rsi => BitVec.ofNat 64 (count operation)
    | .rdx => key
    | other => registers other
  flags := flags
  rip := entry compiler operation
  memory := toMemory (resources compiler operation).shared.resources.space

theorem pre (compiler : Compiler) (operation : Operation) (registers : Register → Word)
    (flags key : Word) (bound : KeyBound operation key) :
    ResourcePre (spec operation) (IndexSearchWindows.bytes compiler operation)
      (resources compiler operation) (machine compiler operation registers flags key) := by
  refine ⟨⟨contract compiler operation, rfl⟩, rfl, rfl, rfl, ?_, ?_⟩
  · cases operation with
    | byte => change 3 < 2^64; decide +kernel
    | u32 => change 2 < 2^64; decide +kernel
  · intro index argument binding
    obtain ⟨index, indexBound⟩ := index
    cases operation with
    | byte =>
      match index with
      | 0 | 1 =>
        simp [spec, taskID, Grading.BufferTask.registeredSpec, Grading.IndexSearch.byteSpec,
          resources] at binding
        subst argument
        rfl
      | 2 =>
        simp [spec, taskID, Grading.BufferTask.registeredSpec, Grading.IndexSearch.byteSpec,
          resources] at binding
        subst argument
        exact bound
      | index + 3 =>
        simp [spec, taskID, Grading.BufferTask.registeredSpec, Grading.IndexSearch.byteSpec] at binding
    | u32 =>
      match index with
      | 0 | 1 =>
        simp [spec, taskID, Grading.BufferTask.registeredSpec, Grading.IndexSearch.u32Spec,
          resources] at binding
        subst argument
        rfl
      | 2 =>
        simp [spec, taskID, Grading.BufferTask.registeredSpec, Grading.IndexSearch.u32Spec,
          resources] at binding
        subst argument
        exact bound
      | index + 3 =>
        simp [spec, taskID, Grading.BufferTask.registeredSpec, Grading.IndexSearch.u32Spec] at binding

theorem raw_pre (compiler : Compiler) (operation : Operation) (registers : Register → Word)
    (flags key : Word) (bound : KeyBound operation key) :
    Pre (spec operation) (IndexSearchWindows.bytes compiler operation)
      (resourceInput (resources compiler operation)) (machine compiler operation registers flags key) :=
  (pre compiler operation registers flags key bound).machine

theorem useful (operation : Operation) : (spec operation).useful (value operation) := by
  cases operation with
  | byte => change ([0x41, 0x42, 0] : List Byte) ≠ []; decide +kernel
  | u32 => change ([0x4241, 0] : List (BitVec 32)) ≠ []; decide +kernel

theorem nonvacuous (compiler : Compiler) (operation : Operation) :
    Grading.ReadOnlyNonvacuous (Grading.BufferTask.registered (taskID operation))
      (IndexSearchWindows.bytes compiler operation) :=
  nonvacuous_of_resource (resources compiler operation)
    (machine compiler operation (fun _ => 0) 0x202 0) (useful operation)
    (pre compiler operation (fun _ => 0) 0x202 0 (by cases operation <;> rfl))

/-- Witness fields consumed by the later root LoadedCall adapter. Task identity
fixes the whole Spec; the caller cannot supply a weaker candidate contract. -/
structure Witness (compiler : Compiler) (operation : Operation) where
  resource : Resources (Grading.BufferTask.registeredSpec (taskID operation))
  initial : X86.State
  useful : (Grading.BufferTask.registeredSpec (taskID operation)).useful resource.value
  pre : ResourcePre (Grading.BufferTask.registeredSpec (taskID operation))
    (IndexSearchWindows.input compiler operation).bytes resource initial
  entry : initial.rip = (IndexSearchWindows.function compiler operation).window.base
  text : ELF.FunctionWindow.TextUnchanged (toMemory (installed compiler operation).space)
    initial.memory (IndexSearchWindows.function compiler operation).window
    (IndexSearchWindows.input compiler operation).bytes.length
  retained : ∀ address original, (installed compiler operation).space.cells address = some original →
    resource.shared.resources.space.cells address = some original
  originalCaller : resource.call.stackLoan = (ByteScanResources.ready compiler).callerLoan
  sysv : (initial.registers .rsp).toNat % 16 = 8 ∧ canonical (initial.registers .rsp) = true
  df : initial.flags.getLsbD 10 = false

def witness (compiler : Compiler) (operation : Operation) : Witness compiler operation :=
  ⟨resources compiler operation, machine compiler operation (fun _ => 0) 0x202 0,
    useful operation, pre compiler operation (fun _ => 0) 0x202 0 (by cases operation <;> rfl),
    rfl, text compiler operation, fun _ _ existing => installed_frame compiler operation existing,
    rfl,
    by change layout.stack.toNat % 16 = 8 ∧ canonical layout.stack = true; decide +kernel,
    by change (0x202 : Word).getLsbD 10 = false; decide +kernel⟩

#print axioms admitted
#print axioms setup_total
#print axioms installed_frame
#print axioms contract
#print axioms pre
#print axioms nonvacuous
#print axioms witness
end EDSL.Corpus.V1.IndexSearchResources
#audit_edsl
