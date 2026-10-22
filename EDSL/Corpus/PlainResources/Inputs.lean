/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.PlainResources.Frozen
import EDSL.Corpus.V1.PlainInputs

/-!
Present loaded resource batches for the independently named frozen plain64
inputs. Every batch retains the same complete installed GCC or Clang ELF,
including full cells/permissions outside the selected function windows. Fresh
managed targets and private protected scalar callers come from the actual
Frozen cohort setup. Both workers' full64 values, counters and logical
occurrences remain arbitrary.

Mixed catalogs and singleton homogeneous catalogs use the same resource
constructor. Singleton admission is restricted only after proving every actual
slot selects that named site. This module constructs present resources, not a
completed execution, behavioral certificate, compiler-preservation proof or
additional corpus credit.
-/

set_option autoImplicit false

namespace EDSL.Corpus.PlainResources.Inputs
open X86 OS OS.AddressSpace Grading.ConcurrentTask

abbrev Compiler := V1.PlainInputs.Compiler
abbrev Kind := Plain64.Kind

/-- The independent interface kind selects the original frozen window kind. -/
def windowKind : Kind → Frozen.Kind := V1.PlainInputs.windowKind

theorem name_eq (kind : Kind) : Plain.name kind = V1.PlainWindows.name (windowKind kind) := by
  cases kind <;> rfl

theorem site_eq (compiler : Compiler) (kind : Kind) :
    Frozen.site compiler (windowKind kind) = V1.PlainInputs.site compiler kind := by
  cases kind <;> rfl

theorem kind_eq (compiler : Compiler) (kind : Kind) :
    (Frozen.site compiler (windowKind kind)).kind = kind := by
  cases kind <;> rfl

theorem catalog_eq (compiler : Compiler) :
    Frozen.catalog compiler = V1.PlainInputs.catalog compiler := rfl

/-- Actual frozen resources for either homogeneous or mixed selected kinds.
The complete original file is retained for every selection and data value. -/
def cohort (compiler : Compiler) (first second : Kind) (old valueA valueB : Word)
    (counterA counterB occurrenceA occurrenceB : Nat) :
    Cohort (Frozen.programSpace compiler) (Frozen.catalog compiler) standard old
      (Frozen.choice compiler (windowKind first) valueA counterA occurrenceA)
      (Frozen.choice compiler (windowKind second) valueB counterB occurrenceB) :=
  Frozen.cohort compiler (windowKind first) (windowKind second) old valueA valueB
    counterA counterB occurrenceA occurrenceB

/-- Both slots' independent inputs name the actual constructor's same cell. -/
theorem inputs_cell {original : Space} {catalog : Plain64.Catalog} {layout : Layout}
    {old : Word} {first second : Choice} (current : Cohort original catalog layout old first second)
    (tid : Fin current.state.workers.length) : (current.inputs tid).cell = current.resources.cell := by
  unfold Cohort.inputs pairInputs
  split <;> exact input_cell _ _ _

theorem target_address (compiler : Compiler) (first second : Kind) (old valueA valueB : Word)
    (counterA counterB occurrenceA occurrenceB : Nat)
    (tid : Fin (cohort compiler first second old valueA valueB
      counterA counterB occurrenceA occurrenceB).state.workers.length) :
    ((cohort compiler first second old valueA valueB
      counterA counterB occurrenceA occurrenceB).inputs tid).cell.address = standard.target := by
  rw [inputs_cell]
  change (Frozen.resources compiler (windowKind first) (windowKind second) old).cell.address = _
  rw [Frozen.resources_cell]
  rfl

/-- Every original loaded address keeps its complete cell, including all
nontext bytes, mappedness and permission bits. -/
theorem retained_image (compiler : Compiler) (first second : Kind) (old valueA valueB : Word)
    (counterA counterB occurrenceA occurrenceB : Nat) (address : Word) (original : AddressSpace.Cell)
    (live : (Frozen.installed compiler).space.cells address = some original) :
    (cohort compiler first second old valueA valueB counterA counterB occurrenceA occurrenceB
      ).state.world.legacy.shared.resources.space.cells address = some original :=
  (cohort compiler first second old valueA valueB counterA counterB occurrenceA occurrenceB
    ).full_image (Frozen.programSpace_eq compiler) live

/-- Target freshness excludes every original loaded cell, rather than only the
selected executable interval or a compiler-specific byte list. -/
theorem targets_fresh (compiler : Compiler) (first second : Kind) (old valueA valueB : Word)
    (counterA counterB occurrenceA occurrenceB : Nat)
    (tid : Fin (cohort compiler first second old valueA valueB
      counterA counterB occurrenceA occurrenceB).state.workers.length)
    (address : Word) (original : AddressSpace.Cell)
    (live : (Frozen.installed compiler).space.cells address = some original) :
    ¬ (qwordRegion ((cohort compiler first second old valueA valueB
      counterA counterB occurrenceA occurrenceB).inputs tid).cell.address).Contains address := by
  intro inside
  rw [target_address] at inside
  have missing := allUnmapped_inside (Frozen.installed compiler).space
    ⟨standard.target, 8⟩
    (Frozen.fresh_regions compiler (windowKind first) (windowKind second) old).1 address inside
  rw [live] at missing
  cases missing

/-- Exact named-file admission for either symbol returns the same complete
installed ELF, with the original unique-name and full-extent checks intact. -/
theorem admitted_named (compiler : Compiler) (kind : Kind) :
    (V1.PlainInputs.named compiler kind).input.admit (V1.PlainWindows.file compiler)
      (Plain.name (V1.PlainInputs.named compiler kind).kind) empty =
        .ok (Frozen.installed compiler) := by
  cases kind <;> exact Frozen.admitted compiler _

/-- Full-cell retention supplies current text preservation for every selected
exact named window in that same complete loaded space. -/
theorem text_named (compiler : Compiler) (first second kind : Kind) (old valueA valueB : Word)
    (counterA counterB occurrenceA occurrenceB : Nat) :
    ELF.FunctionWindow.TextUnchanged (toMemory (Frozen.installed compiler).space)
      (TSO64.published (cohort compiler first second old valueA valueB
        counterA counterB occurrenceA occurrenceB).state.world)
      (V1.PlainInputs.named compiler kind).input.function.window
      (V1.PlainInputs.named compiler kind).input.bytes.length := by
  have installedEq : BufferResources.installed (V1.PlainWindows.file compiler)
      (V1.PlainInputs.named compiler kind).input = Frozen.installed compiler :=
    Frozen.installed_same compiler (windowKind kind)
  have retained : ∀ address original,
      (BufferResources.installed (V1.PlainWindows.file compiler)
        (V1.PlainInputs.named compiler kind).input).space.cells address = some original →
      (cohort compiler first second old valueA valueB counterA counterB occurrenceA occurrenceB
        ).state.world.legacy.shared.resources.space.cells address = some original := by
    intro address original live
    rw [installedEq] at live
    exact retained_image compiler first second old valueA valueB
      counterA counterB occurrenceA occurrenceB address original live
  have text := BufferResources.text_of_retainedWith (V1.PlainInputs.named compiler kind).checked
    (Frozen.executable_permissions compiler) retained
  simpa only [installedEq, TSO64.published] using text

/-- A present batch for any two registered kinds over the full mixed catalog.
No returned workers, completion, method shape or execution result is assumed. -/
def loadedBatch (compiler : Compiler) (first second : Kind) (old valueA valueB : Word)
    (counterA counterB occurrenceA occurrenceB : Nat) :
    Plain.LoadedBatch (V1.PlainWindows.file compiler) (V1.PlainInputs.images compiler) where
  priorSpace := empty
  loaded := Frozen.installed compiler
  admitted := by
    intro selected member
    have alternatives : selected = V1.PlainInputs.named compiler .loadAcquire ∨
        selected = V1.PlainInputs.named compiler .storeRelease := by
      simpa only [V1.PlainInputs.images, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false] using member
    rcases alternatives with rfl | rfl <;> exact admitted_named compiler _
  before := (cohort compiler first second old valueA valueB counterA counterB occurrenceA occurrenceB).state
  inputs := (cohort compiler first second old valueA valueB counterA counterB occurrenceA occurrenceB).inputs
  pre := by
    have admitted := (cohort compiler first second old valueA valueB
      counterA counterB occurrenceA occurrenceB).closedPre
    simpa only [V1.PlainInputs.images_catalog, ← catalog_eq] using admitted
  text := by
    intro selected member
    have alternatives : selected = V1.PlainInputs.named compiler .loadAcquire ∨
        selected = V1.PlainInputs.named compiler .storeRelease := by
      simpa only [V1.PlainInputs.images, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false] using member
    rcases alternatives with rfl | rfl <;>
      exact text_named compiler first second _ old valueA valueB
        counterA counterB occurrenceA occurrenceB
  retainedImage := retained_image compiler first second old valueA valueB
    counterA counterB occurrenceA occurrenceB
  targetsFresh := targets_fresh compiler first second old valueA valueB
    counterA counterB occurrenceA occurrenceB

/-- Mixed store/load resources use both exact named sites from the same full
file and the same fresh managed target. Values and labels remain arbitrary. -/
def mixed (compiler : Compiler) (old storeValue unusedLoadValue : Word)
    (storeCounter loadCounter storeOccurrence loadOccurrence : Nat) :
    Plain.LoadedBatch (V1.PlainWindows.file compiler) (V1.PlainInputs.images compiler) :=
  loadedBatch compiler .storeRelease .loadAcquire old storeValue unusedLoadValue
    storeCounter loadCounter storeOccurrence loadOccurrence

/-- Homogeneous restriction is justified by the sites actually selected at
BOTH slots, rather than by treating the entire mixed catalog as a singleton. -/
theorem homogeneous_site (compiler : Compiler) (kind : Kind) (old valueA valueB : Word)
    (counterA counterB occurrenceA occurrenceB : Nat)
    (tid : Fin (cohort compiler kind kind old valueA valueB
      counterA counterB occurrenceA occurrenceB).state.workers.length) :
    ((cohort compiler kind kind old valueA valueB
      counterA counterB occurrenceA occurrenceB).inputs tid).site = V1.PlainInputs.site compiler kind := by
  unfold Cohort.inputs pairInputs
  split <;> exact (input_site _ _ _).trans (site_eq compiler kind)

/-- Two actual workers at one exact named interface, retaining the entire
installed file and every loaded cell while using the singleton trusted catalog. -/
def homogeneous (compiler : Compiler) (kind : Kind) (old valueA valueB : Word)
    (counterA counterB occurrenceA occurrenceB : Nat) :
    Plain.LoadedBatch (V1.PlainWindows.file compiler) [V1.PlainInputs.named compiler kind] where
  priorSpace := empty
  loaded := Frozen.installed compiler
  admitted := by
    intro selected member
    have same : selected = V1.PlainInputs.named compiler kind := List.mem_singleton.mp member
    subst selected
    exact admitted_named compiler kind
  before := (cohort compiler kind kind old valueA valueB counterA counterB occurrenceA occurrenceB).state
  inputs := (cohort compiler kind kind old valueA valueB counterA counterB occurrenceA occurrenceB).inputs
  pre := by
    let current := cohort compiler kind kind old valueA valueB
      counterA counterB occurrenceA occurrenceB
    refine ⟨?_, current.closedPre.2⟩
    refine ⟨current.pre.valid, ?_, current.pre.entry, current.pre.privateCallers,
      current.pre.codeCallerSeparation⟩
    intro tid
    change (current.inputs tid).site ∈ [(V1.PlainInputs.named compiler kind).site]
    exact List.mem_singleton.mpr
      (homogeneous_site compiler kind old valueA valueB counterA counterB occurrenceA occurrenceB tid)
  text := by
    intro selected member
    have same : selected = V1.PlainInputs.named compiler kind := List.mem_singleton.mp member
    subst selected
    exact text_named compiler kind kind kind old valueA valueB
      counterA counterB occurrenceA occurrenceB
  retainedImage := retained_image compiler kind kind old valueA valueB
    counterA counterB occurrenceA occurrenceB
  targetsFresh := targets_fresh compiler kind kind old valueA valueB
    counterA counterB occurrenceA occurrenceB

end EDSL.Corpus.PlainResources.Inputs

#audit_edsl
