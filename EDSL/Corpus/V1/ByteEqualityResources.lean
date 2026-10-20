/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.ReadOnlyCallTransport
import EDSL.Corpus.V1.ByteComparisonResources
import EDSL.Corpus.V1.ByteEqualityWindows

set_option autoImplicit false
set_option warningAsError true

/-! Reuse the initialized paired-buffer world for another checked function.
Only its code loan and return relation change; no RAM or input loan is rebuilt. -/

namespace EDSL.Corpus.V1.ByteEqualityResources
open X86 OS OS.AddressSpace BufferCall

abbrev Compiler := ByteEqualityWindows.Compiler
abbrev layout := ByteComparisonResources.layout

def taskID : Grading.BufferTask.TaskID := .equalBytes
def spec : Spec := Grading.BufferTask.registeredSpec taskID

def entry (compiler : Compiler) : Word := (ByteEqualityWindows.function compiler).window.base

def installed (compiler : Compiler) : ELF.Loaded :=
  BufferResources.installed (ByteEqualityWindows.file compiler) (ByteEqualityWindows.input compiler)

theorem admitted (compiler : Compiler) :
    (ByteEqualityWindows.input compiler).admitWith (ByteEqualityWindows.maxBytes compiler)
      (ByteEqualityWindows.file compiler) ByteEqualityWindows.name empty = .ok (installed compiler) :=
  BufferResources.admittedWith (ByteEqualityWindows.checked compiler)

theorem installed_seed (compiler : Compiler) :
    installed compiler = ByteComparisonResources.installed compiler := rfl

theorem executable_permissions (compiler : Compiler) :
    ∀ segment ∈ (ByteEqualityWindows.input compiler).table.image.segments,
      segment.permissions.executable = true → segment.permissions = readExecute :=
  ByteComparisonResources.executable_permissions compiler

/-- A faster index of exactly the same complete memory, including the original
caller slot, both overlapping snapshots and every nonfunction ELF cell. -/
def spaceView (compiler : Compiler) : Space :=
  BufferResources.freshQWord
    (BufferResources.freshQWord
      (BufferResources.programSpace (ByteEqualityWindows.file compiler)
        (ByteEqualityWindows.input compiler)) layout.stack layout.returnAddress)
    0x10000 0x4241

theorem spaceView_eq (compiler : Compiler) :
    spaceView compiler = (ByteComparisonResources.resources compiler).shared.resources.space := by
  rw [ByteComparisonResources.space, ← ByteComparisonResources.spaceView_eq]
  unfold spaceView ByteComparisonResources.spaceView
  rw [BufferResources.programSpace_eqWith (ByteEqualityWindows.checked compiler)
      (executable_permissions compiler),
    BufferResources.programSpace_eq (ByteComparisonWindows.checked compiler)
      (ByteComparisonResources.executable_permissions compiler)]
  rfl

def seed (compiler : Compiler) : BufferResources.Managed :=
  ReadOnlyResources.reindex (ByteComparisonResources.ready compiler).managed
    (spaceView compiler) (spaceView_eq compiler)

theorem seed_shared (compiler : Compiler) :
    (seed compiler).shared = (ByteComparisonResources.resources compiler).shared :=
  ReadOnlyResources.reindex_shared _ _ _

def actualSetup (compiler : Compiler) : Except Borrowing.Fault
    (ReadOnlyCalls.Attached (seed compiler)
      (ByteComparisonResources.resources compiler).call.worker
      ⟨entry compiler, (ByteEqualityWindows.bytes compiler).length⟩ []) :=
  ReadOnlyCalls.attach (seed compiler) layout.codeOwner layout.worker
    ⟨entry compiler, (ByteEqualityWindows.bytes compiler).length⟩ []

theorem actualSetup_total (compiler : Compiler) : (actualSetup compiler).toOption.isSome = true := by
  cases compiler <;> buffer_resource_kernel_rfl

def ready (compiler : Compiler) :=
  (actualSetup compiler).toOption.get (actualSetup_total compiler)

theorem code_before (compiler : Compiler) :
    CodeAt (toMemory (ByteComparisonResources.resources compiler).shared.resources.space)
      (entry compiler) (ByteEqualityWindows.bytes compiler) :=
  ELF.FunctionSymbol.admitted_current_codeWith (admitted compiler)
    (BufferResources.text_of_retainedWith (ByteEqualityWindows.checked compiler)
      (executable_permissions compiler) (fun _ _ original =>
        ByteComparisonResources.installed_frame compiler
          (by simpa only [installed_seed] using original)))

def resources (compiler : Compiler) : Resources spec :=
  ReadOnlyCallTransport.resultView
    (ReadOnlyCallTransport.retarget (ByteComparisonResources.resources compiler)
      (ByteEqualityWindows.bytes compiler) (ready compiler)) Grading.ByteEquality.Result

theorem space (compiler : Compiler) :
    (resources compiler).shared.resources.space =
      (ByteComparisonResources.resources compiler).shared.resources.space :=
  ReadOnlyCallTransport.retarget_space _ _ (ready compiler) (seed_shared compiler)

def machine (compiler : Compiler) (registers : Register → Word) (flags : Word) : State :=
  { ByteComparisonResources.machine compiler registers flags with rip := entry compiler }

theorem pre (compiler : Compiler) (registers : Register → Word) (flags : Word) :
    ResourcePre spec (ByteEqualityWindows.bytes compiler) (resources compiler)
      (machine compiler registers flags) :=
  (ReadOnlyCallTransport.resultView_pre_iff _ Grading.ByteEquality.Result _ _).mpr
    (ReadOnlyCallTransport.retarget_pre (ready compiler) (seed_shared compiler)
      (ByteComparisonResources.pre compiler registers flags) (code_before compiler))

theorem useful (compiler : Compiler) : spec.useful (resources compiler).value :=
  ByteComparisonResources.useful

theorem installed_frame (compiler : Compiler) {address : Word} {original : AddressSpace.Cell}
    (present : (installed compiler).space.cells address = some original) :
    (resources compiler).shared.resources.space.cells address = some original := by
  rw [space]
  exact ByteComparisonResources.installed_frame compiler
    (by simpa only [installed_seed] using present)

theorem text (compiler : Compiler) :
    ELF.FunctionWindow.TextUnchanged (toMemory (installed compiler).space)
      (machine compiler (fun _ => 0) 0x202).memory
      (ByteEqualityWindows.function compiler).window (ByteEqualityWindows.bytes compiler).length := by
  have unchanged := BufferResources.text_of_retainedWith (ByteEqualityWindows.checked compiler)
    (executable_permissions compiler) (fun _ _ present => installed_frame compiler present)
  simpa only [machine, ByteComparisonResources.machine, space] using unchanged

#print axioms admitted
#print axioms spaceView_eq
#print axioms actualSetup_total
#print axioms code_before
#print axioms pre
#print axioms installed_frame
#print axioms text
end EDSL.Corpus.V1.ByteEqualityResources
#audit_edsl
