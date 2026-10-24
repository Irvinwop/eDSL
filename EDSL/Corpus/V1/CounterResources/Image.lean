/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.CounterCall
import EDSL.Corpus.PlainResources.Image

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Present resources for two uses of the same complete frozen counter function
in one compiler's complete loaded ELF. The named admission retains the original
files, tables, symbol extents and compiler-specific byte caps. An indexed space
is proved equal to the complete installed space, including non-code mappings.

The actual checked manager adopts the same image twice, initializes two private
protected caller slots and an arbitrary full64 target word, registers that
target and issues two logical handles. Totality is proved for both compilers
and every initial word. All current cells, permissions, loans, handles and
reads below are projections of that operation; successful setup is no premise.

These are modeled present-resource facts, under the imported long-mode/CET-off,
coherent scalar WB RAM, stable translation/no-alias and protected-resource
assumptions. Actors are logical principals, without native identity
authentication. No instruction execution, counter result, progress, physical
OS ownership, hardware/compiler refinement or corpus credit is established.
-/

namespace EDSL.Corpus.V1.CounterResources.Image
open X86 OS OS.AddressSpace

abbrev Compiler := CounterCommon.Compiler

/-- The entire original named counter extent, at its original symbol address. -/
def image (compiler : Compiler) : ScalarCall64.Image :=
  ⟨CounterCommon.base compiler, CounterMixedGraphs.bytes compiler⟩

def installed (compiler : Compiler) : ELF.Loaded :=
  BufferResources.installed (CounterMixedGraphs.file compiler) (CounterMixedGraphs.input compiler)

/-- Admission uses the explicit original cap: GCC 64 and Clang 128 bytes.
In particular the complete 86-byte Clang symbol is never truncated to 64. -/
theorem admitted (compiler : Compiler) :
    (CounterMixedGraphs.input compiler).admitWith (CounterMixedGraphs.caps compiler).maxBytes
      (CounterMixedGraphs.file compiler) CounterMixedGraphs.name empty = .ok (installed compiler) :=
  BufferResources.admittedWith (CounterMixedGraphs.namedChecked compiler)

theorem executable_permissions (compiler : Compiler) :
    ∀ segment ∈ (CounterMixedGraphs.input compiler).table.image.segments,
      segment.permissions.executable = true → segment.permissions = readExecute := by
  cases compiler <;> decide +kernel

theorem installed_cell (compiler : Compiler) (index : Nat)
    (bound : index < (image compiler).bytes.length) :
    (installed compiler).space.cells ((image compiler).base + BitVec.ofNat 64 index) =
      some ⟨(image compiler).bytes[index], readExecute⟩ :=
  BufferResources.installed_cellWith (CounterMixedGraphs.namedChecked compiler)
    (executable_permissions compiler) index bound

/-- A faster function index over the COMPLETE installed ELF space. -/
def programSpace (compiler : Compiler) : Space :=
  BufferResources.programSpace (CounterMixedGraphs.file compiler) (CounterMixedGraphs.input compiler)

theorem programSpace_eq (compiler : Compiler) :
    programSpace compiler = (installed compiler).space :=
  BufferResources.programSpace_eqWith (CounterMixedGraphs.namedChecked compiler)
    (executable_permissions compiler)

theorem image_length (compiler : Compiler) :
    (image compiler).bytes.length =
      (match compiler with | .defaultGCC => 49 | .defaultClang => 86) := by
  cases compiler <;> buffer_resource_kernel_rfl

theorem image_nonempty (compiler : Compiler) : 0 < (image compiler).bytes.length := by
  cases compiler <;> decide +kernel

theorem image_canonical (compiler : Compiler) : canonical (image compiler).base = true := by
  cases compiler <;> decide +kernel

/-- Target allocation after one shared code allocation and two callers.
Its equality to the actual registered descriptor is proved below. -/
def cell : Atomics64.Cell := ⟨7, ⟨3, 0⟩, PlainResources.standard.target⟩

/-- Totality of the actual same-image setup, with a symbolic initial word.
The kernel checks reduction of the real ownership, borrowing and atomic gates. -/
theorem setup_total (compiler : Compiler) (old : Word) :
    (PlainResources.setup (programSpace compiler) (image compiler) (image compiler)
      PlainResources.standard old).toOption.isSome = true := by
  cases compiler <;> buffer_resource_kernel_rfl

def resources (compiler : Compiler) (old : Word) :
    PlainResources.Ready (programSpace compiler) PlainResources.standard old :=
  (PlainResources.setup (programSpace compiler) (image compiler) (image compiler)
    PlainResources.standard old).toOption.get (setup_total compiler old)

theorem resources_setup (compiler : Compiler) (old : Word) :
    PlainResources.setup (programSpace compiler) (image compiler) (image compiler)
      PlainResources.standard old = .ok (resources compiler old) :=
  PlainResources.checked_get _ (setup_total compiler old)

theorem resources_target (compiler : Compiler) (old : Word) :
    (resources compiler old).target = ⟨0⟩ := by
  cases compiler <;> buffer_resource_kernel_rfl

theorem resources_cell (compiler : Compiler) (old : Word) :
    (resources compiler old).cell = cell := by
  cases compiler <;> buffer_resource_kernel_rfl

theorem resources_codes (compiler : Compiler) (old : Word) :
    (resources compiler old).codeA = 0 ∧ (resources compiler old).codeB = 1 := by
  cases compiler <;> constructor <;> buffer_resource_kernel_rfl

theorem resources_callers (compiler : Compiler) (old : Word) :
    (resources compiler old).callerA = 2 ∧ (resources compiler old).callerB = 3 :=
  PlainResources.setup_callerIds (resources_setup compiler old)

theorem resources_atomics (compiler : Compiler) (old : Word) :
    (resources compiler old).atomicA = ⟨0⟩ ∧ (resources compiler old).atomicB = ⟨1⟩ := by
  cases compiler <;> constructor <;> buffer_resource_kernel_rfl

/-- Distinct actual code loans share the same complete function allocation. -/
theorem code_loans (compiler : Compiler) (old : Word) :
    (resources compiler old).managed.world.legacy.shared.loans (resources compiler old).codeA =
      some ⟨⟨0, 0⟩, 23, 11, ⟨(image compiler).base, (image compiler).bytes.length⟩⟩ ∧
    (resources compiler old).managed.world.legacy.shared.loans (resources compiler old).codeB =
      some ⟨⟨0, 0⟩, 23, 12, ⟨(image compiler).base, (image compiler).bytes.length⟩⟩ := by
  cases compiler <;> constructor <;> buffer_resource_kernel_rfl

/-- Actual private caller records, after all setup operations have completed. -/
theorem caller_loans (compiler : Compiler) (old : Word) :
    (resources compiler old).managed.world.legacy.shared.loans (resources compiler old).callerA =
      some ⟨⟨1, 0⟩, 21, 11, ⟨PlainResources.standard.stackA, 8⟩⟩ ∧
    (resources compiler old).managed.world.legacy.shared.loans (resources compiler old).callerB =
      some ⟨⟨2, 0⟩, 22, 12, ⟨PlainResources.standard.stackB, 8⟩⟩ := by
  cases compiler <;> constructor <;> buffer_resource_kernel_rfl

theorem atomic_handles (compiler : Compiler) (old : Word) :
    (resources compiler old).managed.world.handles (resources compiler old).atomicA =
      some ⟨11, (resources compiler old).target⟩ ∧
    (resources compiler old).managed.world.handles (resources compiler old).atomicB =
      some ⟨12, (resources compiler old).target⟩ := by
  cases compiler <;> constructor <;> buffer_resource_kernel_rfl

theorem resources_live (compiler : Compiler) (old : Word) :
    (resources compiler old).managed.world.cells (resources compiler old).target =
      some (resources compiler old).cell :=
  (resources compiler old).live

theorem registered_live (compiler : Compiler) (old : Word) :
    (resources compiler old).managed.world.cells ⟨0⟩ = some cell := by
  simpa only [resources_target, resources_cell] using resources_live compiler old

theorem target_address (compiler : Compiler) (old : Word) :
    (resources compiler old).cell.address = PlainResources.standard.target :=
  (resources compiler old).address

theorem target_valid (compiler : Compiler) (old : Word) :
    Atomics64.ValidCell (resources compiler old).managed.world.legacy.shared
      (resources compiler old).cell :=
  ((resources compiler old).managed.valid.cells _ _ (resources_live compiler old)).2

theorem initial_read (compiler : Compiler) (old : Word) :
    loadQWord (TSO64.published (resources compiler old).managed.world)
      PlainResources.standard.target = .ok old :=
  (resources compiler old).initialRead

theorem caller_readA (compiler : Compiler) (old : Word) :
    Borrowing.loadWord64 (resources compiler old).managed.world.legacy.shared 11
      (resources compiler old).callerA PlainResources.standard.stackA =
      .ok PlainResources.standard.returnA :=
  (resources compiler old).callerReadA

theorem caller_readB (compiler : Compiler) (old : Word) :
    Borrowing.loadWord64 (resources compiler old).managed.world.legacy.shared 12
      (resources compiler old).callerB PlainResources.standard.stackB =
      .ok PlainResources.standard.returnB :=
  (resources compiler old).callerReadB

/-- Retain the exact cell, including EVERY permission bit, at EVERY loaded
address. This includes all mappings outside the indexed counter function. -/
theorem full_image (compiler : Compiler) (old : Word)
    {address : Word} {original : AddressSpace.Cell}
    (live : (installed compiler).space.cells address = some original) :
    (resources compiler old).managed.world.legacy.shared.resources.space.cells address =
      some original := by
  apply (resources compiler old).managed.retained address original
  rw [programSpace_eq]
  exact live

theorem fresh_regions (compiler : Compiler) (old : Word) :
    allUnmapped (installed compiler).space ⟨PlainResources.standard.target, 8⟩ = true ∧
    allUnmapped (installed compiler).space ⟨PlainResources.standard.stackA, 8⟩ = true ∧
    allUnmapped (installed compiler).space ⟨PlainResources.standard.stackB, 8⟩ = true := by
  have ready := resources compiler old
  simpa only [programSpace_eq] using
    And.intro ready.freshTarget (And.intro ready.freshCallerA ready.freshCallerB)

theorem fresh_target (compiler : Compiler) (old : Word) :
    allUnmapped (installed compiler).space ⟨PlainResources.standard.target, 8⟩ = true :=
  (fresh_regions compiler old).1

/-- Current executable bytes follow from explicit-cap original-file admission
AND exact loaded-cell retention through actual setup. -/
theorem code (compiler : Compiler) (old : Word) :
    CodeAt (TSO64.published (resources compiler old).managed.world)
      (image compiler).base (image compiler).bytes := by
  have text := BufferResources.text_of_retainedWith
    (CounterMixedGraphs.namedChecked compiler) (executable_permissions compiler)
    (fun _address _original live => full_image compiler old live)
  exact ELF.FunctionSymbol.admitted_current_codeWith (admitted compiler) text

/-- Both caller allocations remain read-only in the final setup space. -/
theorem caller_protected (compiler : Compiler) (old : Word) :
    PlainResources.allReadOnly (resources compiler old).managed.world.legacy.shared.resources.space
      ⟨PlainResources.standard.stackA, 8⟩ = true ∧
    PlainResources.allReadOnly (resources compiler old).managed.world.legacy.shared.resources.space
      ⟨PlainResources.standard.stackB, 8⟩ = true := by
  cases compiler <;> constructor <;> buffer_resource_kernel_rfl

#print axioms Compiler
#print axioms image
#print axioms installed
#print axioms admitted
#print axioms executable_permissions
#print axioms installed_cell
#print axioms programSpace
#print axioms programSpace_eq
#print axioms image_length
#print axioms image_nonempty
#print axioms image_canonical
#print axioms cell
#print axioms setup_total
#print axioms resources
#print axioms resources_setup
#print axioms resources_target
#print axioms resources_cell
#print axioms resources_codes
#print axioms resources_callers
#print axioms resources_atomics
#print axioms code_loans
#print axioms caller_loans
#print axioms atomic_handles
#print axioms resources_live
#print axioms registered_live
#print axioms target_address
#print axioms target_valid
#print axioms initial_read
#print axioms caller_readA
#print axioms caller_readB
#print axioms full_image
#print axioms fresh_regions
#print axioms fresh_target
#print axioms code
#print axioms caller_protected

end EDSL.Corpus.V1.CounterResources.Image
#audit_edsl
