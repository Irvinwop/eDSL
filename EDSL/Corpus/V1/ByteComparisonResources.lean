/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.ReadOnlyCalls
import EDSL.Corpus.V1.ByteScanResources
import EDSL.Corpus.V1.ByteComparisonWindows
import EDSL.Grading.BufferTask

set_option autoImplicit false
set_option warningAsError true

/-! Useful present calls for both full frozen memcmp windows. Only the checked
byte-scan initialization is reused. Both overlapping input extents receive new
exact read loans in that same manager, without writing any new RAM. No body,
execution result or semantic certificate is an admission premise. -/

namespace EDSL.Corpus.V1.ByteComparisonResources
open X86 OS OS.AddressSpace BufferCall

abbrev Compiler := ByteComparisonWindows.Compiler
abbrev layout := ByteScanResources.layout

def taskID : Grading.BufferTask.TaskID := .lexicographicBytes
def spec : Spec := Grading.BufferTask.registeredSpec taskID

def entry (compiler : Compiler) : Word := (ByteComparisonWindows.function compiler).window.base

def installed (compiler : Compiler) : ELF.Loaded :=
  BufferResources.installed (ByteComparisonWindows.file compiler) (ByteComparisonWindows.input compiler)

theorem admitted (compiler : Compiler) :
    (ByteComparisonWindows.input compiler).admit (ByteComparisonWindows.file compiler)
      ByteComparisonWindows.name empty = .ok (installed compiler) :=
  BufferResources.admitted (ByteComparisonWindows.checked compiler)

theorem installed_seed (compiler : Compiler) :
    installed compiler = ByteScanResources.installed compiler := rfl

theorem executable_permissions (compiler : Compiler) :
    ∀ segment ∈ (ByteComparisonWindows.input compiler).table.image.segments,
      segment.permissions.executable = true → segment.permissions = readExecute :=
  ByteScanResources.executable_permissions compiler

def value : Grading.ByteComparison.Input := ⟨0x10000, 0x10001, [0x41, 0x42, 0], [0x42, 0, 0]⟩
def left : Buffer := Grading.ByteComparison.leftBuffer value
def right : Buffer := Grading.ByteComparison.rightBuffer value

/-- The original data ticket covers the full initialized eight-byte allocation.
The right three-byte span extends past the old three-byte loan. -/
def requests : List ReadOnlyInputs.Request :=
  [⟨layout.dataOwner, ⟨2, 0⟩, left⟩, ⟨layout.dataOwner, ⟨2, 0⟩, right⟩]

/-- A faster authenticated code index for the complete same ELF and the two
existing initialized qwords; equality below transports the original manager. -/
def spaceView (compiler : Compiler) : Space :=
  BufferResources.freshQWord
    (BufferResources.freshQWord
      (BufferResources.programSpace (ByteComparisonWindows.file compiler)
        (ByteComparisonWindows.input compiler)) layout.stack layout.returnAddress)
    0x10000 0x4241

theorem spaceView_eq (compiler : Compiler) :
    spaceView compiler = (ByteScanResources.resources compiler).shared.resources.space := by
  rw [ByteScanResources.space]
  unfold spaceView ByteScanResources.spaceView
  rw [BufferResources.programSpace_eq (ByteComparisonWindows.checked compiler)
    (executable_permissions compiler), ByteScanResources.programSpace_eq]
  rfl

def seed (compiler : Compiler) : BufferResources.Managed :=
  ReadOnlyResources.reindex (ByteScanResources.ready compiler).managed
    (spaceView compiler) (spaceView_eq compiler)

theorem seed_shared (compiler : Compiler) :
    (seed compiler).shared = (ByteScanResources.resources compiler).shared :=
  ReadOnlyResources.reindex_shared _ _ _

def actualSetup (compiler : Compiler) :
    Except Borrowing.Fault (ReadOnlyCalls.Attached (seed compiler) layout.worker
      ⟨entry compiler, (ByteComparisonWindows.bytes compiler).length⟩ requests) :=
  ReadOnlyCalls.attach (seed compiler) layout.codeOwner layout.worker
    ⟨entry compiler, (ByteComparisonWindows.bytes compiler).length⟩ requests

theorem actualSetup_total (compiler : Compiler) : (actualSetup compiler).toOption.isSome = true := by
  cases compiler <;> buffer_resource_kernel_rfl

def ready (compiler : Compiler) :=
  (actualSetup compiler).toOption.get (actualSetup_total compiler)

def resources (compiler : Compiler) : Resources (Grading.BufferTask.registeredSpec taskID) :=
  ⟨(ready compiler).managed.shared,
    ⟨layout.worker, entry compiler, layout.stack, layout.returnAddress,
      ByteComparisonWindows.bytes compiler, (ready compiler).codeLoan,
      (ByteScanResources.ready compiler).callerLoan⟩,
    value, fun buffer => if buffer = left then ((ready compiler).inputs.identifiers[0]?).getD 0
      else ((ready compiler).inputs.identifiers[1]?).getD 0⟩

theorem space (compiler : Compiler) :
    (resources compiler).shared.resources.space =
      (ByteScanResources.resources compiler).shared.resources.space :=
  (ready compiler).space.trans
    (congrArg (fun shared : Borrowing.State => shared.resources.space) (seed_shared compiler))

theorem checked_history (compiler : Compiler) :
    Borrowing.History (ByteScanResources.resources compiler).shared (resources compiler).shared := by
  rw [← seed_shared compiler]
  exact (ready compiler).history

theorem original_loans (compiler : Compiler) {identifier : Nat} {loan : Borrowing.Loan}
    (live : (ByteScanResources.resources compiler).shared.loans identifier = some loan) :
    (resources compiler).shared.loans identifier = some loan :=
  (ready compiler).loans _ _ (by simpa only [seed_shared] using live)

theorem original_allocations (compiler : Compiler) {identifier : Nat}
    {allocation : Ownership.Allocation}
    (live : (ByteScanResources.resources compiler).shared.resources.allocations identifier = some allocation) :
    (resources compiler).shared.resources.allocations identifier = some allocation :=
  (ready compiler).allocations _ _ (by simpa only [seed_shared] using live)

/-- Every installed cell, including permissions and noncode ELF segments,
survives initialization and the checked code/input borrowing extension. -/
theorem installed_frame (compiler : Compiler) {address : Word} {original : AddressSpace.Cell}
    (existing : (installed compiler).space.cells address = some original) :
    (resources compiler).shared.resources.space.cells address = some original := by
  rw [space]
  exact ByteScanResources.installed_frame compiler (by simpa only [installed_seed] using existing)

theorem text (compiler : Compiler) :
    ELF.FunctionWindow.TextUnchanged (toMemory (installed compiler).space)
      (toMemory (resources compiler).shared.resources.space)
      (ByteComparisonWindows.function compiler).window (ByteComparisonWindows.bytes compiler).length := by
  intro index bound
  have original := BufferResources.installed_cell (ByteComparisonWindows.checked compiler)
    (executable_permissions compiler) index bound
  have present := installed_frame compiler original
  change (installed compiler).space.cells
    ((ByteComparisonWindows.function compiler).window.base + BitVec.ofNat 64 index) =
      some ⟨(ByteComparisonWindows.bytes compiler)[index], readExecute⟩ at original
  change (resources compiler).shared.resources.space.cells
    ((ByteComparisonWindows.function compiler).window.base + BitVec.ofNat 64 index) =
      some ⟨(ByteComparisonWindows.bytes compiler)[index], readExecute⟩ at present
  constructor <;> simp only [toMemory, present, original] <;> rfl

theorem current_code (compiler : Compiler) :
    CodeAt (toMemory (resources compiler).shared.resources.space) (entry compiler)
      (ByteComparisonWindows.bytes compiler) :=
  ELF.FunctionSymbol.admitted_current_code (admitted compiler) (text compiler)

theorem code_held (compiler : Compiler) :
    Threads.HasLoan (resources compiler).shared layout.worker (resources compiler).call.codeLoan
      ⟨entry compiler, (ByteComparisonWindows.bytes compiler).length⟩ :=
  (ready compiler).codeHeld

theorem caller_held (compiler : Compiler) :
    Threads.HasLoan (resources compiler).shared layout.worker (resources compiler).call.stackLoan
      ⟨layout.stack, 8⟩ :=
  (ready compiler).original_loan (by
    change Threads.HasLoan (seed compiler).shared layout.worker
      (ByteScanResources.ready compiler).callerLoan ⟨layout.stack, 8⟩
    rw [seed_shared]
    exact ByteScanResources.caller_held compiler)

theorem caller_private (compiler : Compiler) :
    Ownership.authorize (resources compiler).shared.resources layout.callerOwner ⟨1, 0⟩ =
      .ok ⟨layout.callerOwner, 0, ⟨layout.stack, 8⟩⟩ :=
  (ready compiler).authorize
    (by simpa only [seed_shared] using (ByteScanResources.caller_abi compiler (fun _ => 0)).2.2.2)

theorem left_held (compiler : Compiler) :
    Threads.HasLoan (resources compiler).shared layout.worker
      ((resources compiler).inputLoan left) left.region := by
  change Threads.HasLoan (ready compiler).inputs.managed.shared layout.worker
    (((ready compiler).inputs.identifiers[0]?).getD 0) left.region
  exact (ready compiler).inputs.held 0 ⟨layout.dataOwner, ⟨2, 0⟩, left⟩ rfl (by decide +kernel)

theorem right_held (compiler : Compiler) :
    Threads.HasLoan (resources compiler).shared layout.worker
      ((resources compiler).inputLoan right) right.region := by
  change Threads.HasLoan (ready compiler).inputs.managed.shared layout.worker
    (((ready compiler).inputs.identifiers[1]?).getD 0) right.region
  exact (ready compiler).inputs.held 1 ⟨layout.dataOwner, ⟨2, 0⟩, right⟩ rfl (by decide +kernel)

theorem caller_read (compiler : Compiler) :
    readWord (toMemory (resources compiler).shared.resources.space) layout.stack =
      .ok layout.returnAddress := by
  rw [space]
  exact ByteScanResources.caller_read compiler

theorem left_snapshot (compiler : Compiler) :
    BufferAt (toMemory (resources compiler).shared.resources.space) left.base left.bytes := by
  rw [space]
  exact ByteScanResources.buffer_snapshot compiler

theorem right_snapshot (compiler : Compiler) :
    BufferAt (toMemory (resources compiler).shared.resources.space) right.base right.bytes := by
  rw [space, ByteScanResources.space]
  refine ⟨by decide +kernel, ?_⟩
  intro index byte present
  match index with
  | 0 | 1 | 2 => simp [right, value, Grading.ByteComparison.rightBuffer] at present; subst byte; rfl
  | index + 3 => simp [right, value, Grading.ByteComparison.rightBuffer] at present

theorem contract (compiler : Compiler) :
    ResourceContract (resources compiler) (resources compiler).shared := by
  apply Grading.ByteComparison.resourceContract_iff _ _ |>.mpr
  refine ⟨⟨(ready compiler).managed.valid, code_held compiler, caller_held compiler,
    current_code compiler, caller_read compiler, ?_, ?_, ?_⟩,
    left_snapshot compiler, right_snapshot compiler, fun _ => left_held compiler,
    fun _ => right_held compiler⟩
  · exact (ByteScanResources.contract compiler).call.returnCanonical
  · exact (ByteScanResources.contract compiler).call.stackBound
  · exact (ByteScanResources.contract compiler).call.postStackCanonical

/-- Other registers and flags are arbitrary. All three arguments and the full
original caller stack are bound independently of any execution. -/
def machine (compiler : Compiler) (registers : Register → Word) (flags : Word) : X86.State where
  registers register := match register with
    | .rsp => layout.stack
    | .rdi => value.leftBase
    | .rsi => value.rightBase
    | .rdx => BitVec.ofNat 64 value.left.length
    | other => registers other
  flags := flags
  rip := entry compiler
  memory := toMemory (resources compiler).shared.resources.space

theorem pre (compiler : Compiler) (registers : Register → Word) (flags : Word) :
    ResourcePre spec (ByteComparisonWindows.bytes compiler) (resources compiler)
      (machine compiler registers flags) := by
  refine ⟨⟨contract compiler, rfl⟩, rfl, rfl, rfl, ?_, ?_⟩
  · change value.left.length = value.right.length ∧ value.left.length < 2^64
    decide +kernel
  · exact (Grading.ByteComparison.bound_iff _ _).mpr ⟨rfl, rfl, rfl⟩

theorem raw_pre (compiler : Compiler) (registers : Register → Word) (flags : Word) :
    Pre spec (ByteComparisonWindows.bytes compiler) (resourceInput (resources compiler))
      (machine compiler registers flags) := (pre compiler registers flags).machine

theorem useful : spec.useful value := by
  change value.left ≠ []
  decide +kernel

theorem nonvacuous (compiler : Compiler) :
    Grading.ReadOnlyNonvacuous (Grading.BufferTask.registered taskID)
      (ByteComparisonWindows.bytes compiler) :=
  nonvacuous_of_resource (resources compiler) (machine compiler (fun _ => 0) 0x202)
    useful (pre compiler (fun _ => 0) 0x202)

/-- Ready for composition with the separate universal body proof. The task
fixes the whole registered spec; there is no candidate-supplied result field. -/
structure Witness (compiler : Compiler) where
  resource : Resources (Grading.BufferTask.registeredSpec taskID)
  initial : X86.State
  useful : (Grading.BufferTask.registeredSpec taskID).useful resource.value
  pre : ResourcePre (Grading.BufferTask.registeredSpec taskID)
    (ByteComparisonWindows.input compiler).bytes resource initial
  entry : initial.rip = (ByteComparisonWindows.function compiler).window.base
  text : ELF.FunctionWindow.TextUnchanged (toMemory (installed compiler).space) initial.memory
    (ByteComparisonWindows.function compiler).window (ByteComparisonWindows.input compiler).bytes.length
  retained : ∀ address original, (installed compiler).space.cells address = some original →
    resource.shared.resources.space.cells address = some original
  originalCaller : resource.call.stackLoan = (ByteScanResources.ready compiler).callerLoan
  sysv : (initial.registers .rsp).toNat % 16 = 8 ∧ canonical (initial.registers .rsp) = true
  df : initial.flags.getLsbD 10 = false

def witness (compiler : Compiler) : Witness compiler :=
  ⟨resources compiler, machine compiler (fun _ => 0) 0x202, useful,
    pre compiler (fun _ => 0) 0x202, rfl, text compiler,
    fun _ _ existing => installed_frame compiler existing, rfl,
    by change layout.stack.toNat % 16 = 8 ∧ canonical layout.stack = true; decide +kernel,
    by change (0x202 : Word).getLsbD 10 = false; decide +kernel⟩

def gccWitness : Witness .defaultGCC := witness .defaultGCC
def clangWitness : Witness .defaultClang := witness .defaultClang

#print axioms admitted
#print axioms installed_seed
#print axioms spaceView_eq
#print axioms actualSetup_total
#print axioms checked_history
#print axioms original_loans
#print axioms original_allocations
#print axioms installed_frame
#print axioms text
#print axioms current_code
#print axioms code_held
#print axioms caller_held
#print axioms caller_private
#print axioms left_held
#print axioms right_held
#print axioms left_snapshot
#print axioms right_snapshot
#print axioms contract
#print axioms pre
#print axioms raw_pre
#print axioms useful
#print axioms nonvacuous
#print axioms witness
#print axioms gccWitness
#print axioms clangWitness
end EDSL.Corpus.V1.ByteComparisonResources
#audit_edsl
