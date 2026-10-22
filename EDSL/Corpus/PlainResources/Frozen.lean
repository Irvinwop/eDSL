/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.PlainResources.Image
import EDSL.Corpus.V1.PlainWindows

set_option autoImplicit false
set_option warningAsError true

/-! Source instantiation of the generic resource provider with the unchanged
complete frozen ELF files. Named-file checking and complete static shapes stay
separate from the independent present-state Pre. No execution proof, whole
Claim, compiler preservation or additional corpus total is declared here. -/

namespace EDSL.Corpus.PlainResources.Frozen
open X86 OS OS.AddressSpace Grading.ConcurrentTask

abbrev Compiler := V1.PlainWindows.Compiler
abbrev Kind := V1.PlainWindows.Kind

def image (compiler : Compiler) (kind : Kind) : ScalarCall64.Image :=
  ⟨(V1.PlainWindows.function compiler kind).window.base, V1.PlainWindows.bytes compiler kind⟩

def site (compiler : Compiler) (kind : Kind) : Plain64.Site :=
  ⟨match kind with | .loadAcquire => .loadAcquire | .storeRelease => .storeRelease,
    image compiler kind⟩

def catalog (compiler : Compiler) : Plain64.Catalog :=
  [site compiler .loadAcquire, site compiler .storeRelease]

def choice (compiler : Compiler) (kind : Kind) (value : Word) (counter occurrence : Nat) : Choice :=
  ⟨site compiler kind, value, counter, occurrence⟩

def installed (compiler : Compiler) : ELF.Loaded :=
  BufferResources.installed (V1.PlainWindows.file compiler) (V1.PlainWindows.input compiler .loadAcquire)

theorem installed_same (compiler : Compiler) (kind : Kind) :
    BufferResources.installed (V1.PlainWindows.file compiler) (V1.PlainWindows.input compiler kind) =
      installed compiler := rfl

/-- The existing unique-name/full-extent/full-file check is unchanged. Actual
symbol indices remain GCC115/140 and Clang92/116 through PlainWindows.input. -/
theorem admitted (compiler : Compiler) (kind : Kind) :
    (V1.PlainWindows.input compiler kind).admit (V1.PlainWindows.file compiler)
      (V1.PlainWindows.name kind) empty = .ok (installed compiler) :=
  BufferResources.admitted (V1.PlainWindows.checked compiler kind)

theorem executable_permissions (compiler : Compiler) :
    ∀ segment ∈ (V1.PlainWindows.input compiler .loadAcquire).table.image.segments,
      segment.permissions.executable = true → segment.permissions = readExecute := by
  cases compiler <;> decide +kernel

/-- Both checked slices have fast indices in the SAME complete installed
space. Neither slice is a replacement image or an opcode-only fixture. -/
def programSpace (compiler : Compiler) : Space :=
  indexSlice (indexSlice (installed compiler).space (image compiler .loadAcquire))
    (image compiler .storeRelease)

theorem programSpace_eq (compiler : Compiler) : programSpace compiler = (installed compiler).space := by
  have slice (kind : Kind) (index : Nat) (bound : index < (image compiler kind).bytes.length) :
      (installed compiler).space.cells ((image compiler kind).base + BitVec.ofNat 64 index) =
        some ⟨(image compiler kind).bytes[index], readExecute⟩ :=
    BufferResources.installed_cell (V1.PlainWindows.checked compiler kind)
      (executable_permissions compiler) index bound
  have load := indexSlice_eq (installed compiler).space (image compiler .loadAcquire) (slice .loadAcquire)
  have store := indexSlice_eq (installed compiler).space (image compiler .storeRelease) (slice .storeRelease)
  unfold programSpace
  rw [load, store]

def extra (first second : Kind) : Nat := if first = second then 0 else 1

def cell (first second : Kind) : Atomics64.Cell := ⟨7, ⟨3 + extra first second, 0⟩, standard.target⟩

theorem setup_total (compiler : Compiler) (first second : Kind) (old : Word) :
    (setup (programSpace compiler) (image compiler first) (image compiler second) standard old).toOption.isSome = true := by
  cases compiler <;> cases first <;> cases second <;> buffer_resource_kernel_rfl

def resources (compiler : Compiler) (first second : Kind) (old : Word) :
    Ready (programSpace compiler) standard old :=
  (setup (programSpace compiler) (image compiler first) (image compiler second) standard old).toOption.get
    (setup_total compiler first second old)

theorem resources_setup (compiler : Compiler) (first second : Kind) (old : Word) :
    setup (programSpace compiler) (image compiler first) (image compiler second) standard old =
      .ok (resources compiler first second old) :=
  checked_get _ (setup_total compiler first second old)

theorem resources_target (compiler : Compiler) (first second : Kind) (old : Word) :
    (resources compiler first second old).target = ⟨0⟩ := by
  cases compiler <;> cases first <;> cases second <;> buffer_resource_kernel_rfl

theorem resources_cell (compiler : Compiler) (first second : Kind) (old : Word) :
    (resources compiler first second old).cell = cell first second := by
  cases compiler <;> cases first <;> cases second <;> buffer_resource_kernel_rfl

theorem start_total (compiler : Compiler) (first second : Kind) (old valueA valueB : Word)
    (counterA counterB occurrenceA occurrenceB : Nat) :
    (start (resources compiler first second old)
      (choice compiler first valueA counterA occurrenceA)
      (choice compiler second valueB counterB occurrenceB)).toOption.isSome = true := by
  cases compiler <;> cases first <;> cases second <;> buffer_resource_kernel_rfl

def started (compiler : Compiler) (first second : Kind) (old valueA valueB : Word)
    (counterA counterB occurrenceA occurrenceB : Nat) :
    Checked (resources compiler first second old).managed.world :=
  (start (resources compiler first second old)
    (choice compiler first valueA counterA occurrenceA)
    (choice compiler second valueB counterB occurrenceB)).toOption.get
      (start_total compiler first second old valueA valueB counterA counterB occurrenceA occurrenceB)

def actor (tid : Fin 2) : Nat := if tid.val = 0 then 11 else 12
def stack (tid : Fin 2) : Word := if tid.val = 0 then standard.stackA else standard.stackB
def continuation (tid : Fin 2) : Word := if tid.val = 0 then standard.returnA else standard.returnB
def selectedKind (first second : Kind) (tid : Fin 2) : Kind := if tid.val = 0 then first else second
def selectedWord (first second : Word) (tid : Fin 2) : Word := if tid.val = 0 then first else second
def selectedNat (first second : Nat) (tid : Fin 2) : Nat := if tid.val = 0 then first else second

/-- An authenticated projection of the actual attached workers, used only for
normalization. Authority and validity come from setup/start and their existing
preservation theorems, rather than this descriptive record. -/
def workerView (compiler : Compiler) (first second : Kind) (valueA valueB : Word)
    (counterA counterB : Nat) (tid : Fin 2) : TSO64.Worker where
  context := context (image compiler (selectedKind first second tid)) (cell first second).address
    (stack tid) (selectedWord valueA valueB tid)
  resources := {
    actor := actor tid
    code := ⟨tid.val, ⟨⟨if tid.val = 0 then 0 else extra first second, 0⟩, 23, actor tid,
      ⟨(image compiler (selectedKind first second tid)).base,
        (image compiler (selectedKind first second tid)).bytes.length⟩⟩⟩
    caller := ⟨tid.val + 2, ⟨⟨1 + extra first second + tid.val, 0⟩, 21 + tid.val,
      actor tid, ⟨stack tid, 8⟩⟩⟩
    callerAddress := stack tid
    grants := []
    atomics := [⟨tid.val⟩] }
  phase := .running
  pending := []
  nextStore := selectedNat counterA counterB tid

theorem workers_view (compiler : Compiler) (first second : Kind) (old valueA valueB : Word)
    (counterA counterB occurrenceA occurrenceB : Nat) :
    (started compiler first second old valueA valueB counterA counterB occurrenceA occurrenceB).state.workers =
      [workerView compiler first second valueA valueB counterA counterB 0,
        workerView compiler first second valueA valueB counterA counterB 1] := by
  cases compiler <;> cases first <;> cases second <;> buffer_resource_kernel_rfl

def state (compiler : Compiler) (first second : Kind) (old valueA valueB : Word)
    (counterA counterB : Nat) : TSO64.State :=
  ⟨(resources compiler first second old).managed.world,
    [workerView compiler first second valueA valueB counterA counterB 0,
      workerView compiler first second valueA valueB counterA counterB 1]⟩

theorem started_state (compiler : Compiler) (first second : Kind) (old valueA valueB : Word)
    (counterA counterB occurrenceA occurrenceB : Nat) :
    (started compiler first second old valueA valueB counterA counterB occurrenceA occurrenceB).state =
      state compiler first second old valueA valueB counterA counterB :=
  state_pair (started compiler first second old valueA valueB counterA counterB occurrenceA occurrenceB).sameWorld
    (workers_view compiler first second old valueA valueB counterA counterB occurrenceA occurrenceB)

theorem full_image (compiler : Compiler) (first second : Kind) (old : Word)
    {address : Word} {original : AddressSpace.Cell}
    (live : (installed compiler).space.cells address = some original) :
    (resources compiler first second old).managed.world.legacy.shared.resources.space.cells address = some original := by
  apply (resources compiler first second old).managed.retained address original
  rw [programSpace_eq]
  exact live

theorem fresh_regions (compiler : Compiler) (first second : Kind) (old : Word) :
    allUnmapped (installed compiler).space ⟨standard.target, 8⟩ = true ∧
    allUnmapped (installed compiler).space ⟨standard.stackA, 8⟩ = true ∧
    allUnmapped (installed compiler).space ⟨standard.stackB, 8⟩ = true := by
  have ready := resources compiler first second old
  simpa only [programSpace_eq] using
    And.intro ready.freshTarget (And.intro ready.freshCallerA ready.freshCallerB)

theorem initial_read (compiler : Compiler) (first second : Kind) (old : Word) :
    loadQWord (TSO64.published (resources compiler first second old).managed.world)
      standard.target = .ok old :=
  (resources compiler first second old).initialRead

theorem code (compiler : Compiler) (first second : Kind) (old : Word) (kind : Kind) :
    CodeAt (TSO64.published (resources compiler first second old).managed.world)
      (image compiler kind).base (image compiler kind).bytes := by
  have text := BufferResources.text_of_retainedWith
    (V1.PlainWindows.checked compiler kind) (executable_permissions compiler)
    (fun address original live => full_image compiler first second old live)
  exact ELF.FunctionSymbol.admitted_current_code (admitted compiler kind) text

theorem selection (compiler : Compiler) (first second : Kind) (old valueA valueB : Word)
    (counterA counterB : Nat) (tid : Fin 2) :
    TSO64.atomicFor (resources compiler first second old).managed.world
      (workerView compiler first second valueA valueB counterA counterB tid).resources
      (cell first second).address =
      some (⟨tid.val⟩, ⟨actor tid, ⟨0⟩⟩, cell first second) := by
  rcases tid with ⟨tid, bound⟩
  have cases : tid = 0 ∨ tid = 1 := by omega
  rcases cases with rfl | rfl <;> cases compiler <;> cases first <;> cases second <;>
    buffer_resource_kernel_rfl

/-- The original caller identifiers are derived once from the actual setup's
loan frontier. Caller data and the complete installed space remain arbitrary. -/
theorem resources_callers (compiler : Compiler) (first second : Kind) (old : Word) :
    (resources compiler first second old).callerA = 2 ∧
      (resources compiler first second old).callerB = 3 :=
  setup_callerIds (resources_setup compiler first second old)

theorem caller_read (compiler : Compiler) (first second : Kind) (old valueA valueB : Word)
    (counterA counterB : Nat) (tid : Fin 2) :
    Borrowing.loadWord64 (resources compiler first second old).managed.world.legacy.shared
      (workerView compiler first second valueA valueB counterA counterB tid).resources.actor
      (workerView compiler first second valueA valueB counterA counterB tid).resources.caller.identifier
      (workerView compiler first second valueA valueB counterA counterB tid).resources.callerAddress =
      .ok (continuation tid) := by
  rcases tid with ⟨tid, bound⟩
  have cases : tid = 0 ∨ tid = 1 := by omega
  rcases cases with rfl | rfl
  · change Borrowing.loadWord64 (resources compiler first second old).managed.world.legacy.shared
      11 2 standard.stackA = .ok standard.returnA
    simpa only [(resources_callers compiler first second old).1] using
      (resources compiler first second old).callerReadA
  · change Borrowing.loadWord64 (resources compiler first second old).managed.world.legacy.shared
      12 3 standard.stackB = .ok standard.returnB
    simpa only [(resources_callers compiler first second old).2] using
      (resources compiler first second old).callerReadB

theorem caller_protected (compiler : Compiler) (first second : Kind) (old valueA valueB : Word)
    (counterA counterB : Nat) (tid : Fin 2) :
    allReadOnly (resources compiler first second old).managed.world.legacy.shared.resources.space
      (workerView compiler first second valueA valueB counterA counterB tid).resources.caller.loan.region = true := by
  rcases tid with ⟨tid, bound⟩
  have cases : tid = 0 ∨ tid = 1 := by omega
  rcases cases with rfl | rfl <;> cases compiler <;> cases first <;> cases second <;>
    buffer_resource_kernel_rfl

theorem scalar (compiler : Compiler) (first second : Kind) (valueA valueB : Word)
    (counterA counterB : Nat) (tid : Fin 2) :
    ScalarCall64.Entry (workerView compiler first second valueA valueB counterA counterB tid) := by
  rcases tid with ⟨tid, bound⟩
  have cases : tid = 0 ∨ tid = 1 := by omega
  rcases cases with rfl | rfl
  · refine ⟨?_, ?_, ?_, ?_⟩
    · change ((0x700008 : Word).toNat + 8) % 16 = 0; decide +kernel
    · change (0x202 : Word).getLsbD 10 = false; decide +kernel
    · change (0x700008 : Word).toNat + 8 < 2^64; decide +kernel
    · change canonical ((0x700008 : Word) + 8) = true; decide +kernel
  · refine ⟨?_, ?_, ?_, ?_⟩
    · change ((0x710008 : Word).toNat + 8) % 16 = 0; decide +kernel
    · change (0x202 : Word).getLsbD 10 = false; decide +kernel
    · change (0x710008 : Word).toNat + 8 < 2^64; decide +kernel
    · change canonical ((0x710008 : Word) + 8) = true; decide +kernel

theorem image_nonempty (compiler : Compiler) (kind : Kind) :
    0 < (image compiler kind).bytes.length := by
  cases compiler <;> cases kind <;> decide +kernel

theorem image_canonical (compiler : Compiler) (kind : Kind) :
    canonical (image compiler kind).base = true := by
  cases compiler <;> cases kind <;> decide +kernel

theorem continuation_canonical (tid : Fin 2) : canonical (continuation tid) = true := by
  rcases tid with ⟨tid, bound⟩
  have cases : tid = 0 ∨ tid = 1 := by omega
  rcases cases with rfl | rfl
  · change canonical (0x654320 : Word) = true; decide +kernel
  · change canonical (0x654330 : Word) = true; decide +kernel

theorem entry (compiler : Compiler) (first second : Kind) (old valueA valueB : Word)
    (counterA counterB occurrenceA occurrenceB : Nat) (tid : Fin 2) :
    Plain64.Entry
      (input (choice compiler (selectedKind first second tid) (selectedWord valueA valueB tid)
        (selectedNat counterA counterB tid) (selectedNat occurrenceA occurrenceB tid))
        (resources compiler first second old).target (resources compiler first second old).cell)
      (state compiler first second old valueA valueB counterA counterB)
      (workerView compiler first second valueA valueB counterA counterB tid) := by
  have live : (resources compiler first second old).managed.world.cells ⟨0⟩ = some (cell first second) := by
    simpa only [resources_target, resources_cell] using (resources compiler first second old).live
  rw [resources_target, resources_cell]
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl,
    scalar compiler first second valueA valueB counterA counterB tid, ?_, ?_, ?_, ?_⟩
  · rw [input_site]; rfl
  · apply arguments_of_registers
    · rw [input_cell]; rfl
    · cases selected : selectedKind first second tid <;>
        simp [secondArgument, input, choice, site, selected, workerView, context]
  · simpa only [input_site, choice, site] using image_nonempty compiler (selectedKind first second tid)
  · simpa only [input_site, choice, site] using image_canonical compiler (selectedKind first second tid)
  · simpa only [input_site, choice, site, state] using code compiler first second old (selectedKind first second tid)
  · rw [input_site]
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  · simpa only [input_target, input_cell, state] using live
  · simpa only [input_cell, state] using ((resources compiler first second old).managed.valid.cells _ _ live).2
  · refine ⟨⟨tid.val⟩, ⟨actor tid, ⟨0⟩⟩, ?_, ?_⟩
    · simpa only [input_cell, state] using selection compiler first second old valueA valueB counterA counterB tid
    · rw [input_target]
  · exact ⟨continuation tid,
      caller_read compiler first second old valueA valueB counterA counterB tid,
      continuation_canonical tid⟩

theorem members (compiler : Compiler) (kind : Kind) : site compiler kind ∈ catalog compiler := by
  cases kind <;> simp [catalog]

theorem private_callers (compiler : Compiler) (first second : Kind) (valueA valueB : Word)
    (counterA counterB : Nat) :
    Ownership.Disjoint
      (workerView compiler first second valueA valueB counterA counterB 0).resources.caller.loan.region
      (workerView compiler first second valueA valueB counterA counterB 1).resources.caller.loan.region := by
  change Ownership.Disjoint ⟨standard.stackA, 8⟩ ⟨standard.stackB, 8⟩
  decide +kernel

theorem code_caller (compiler : Compiler) (kind : Kind) (first second : Kind) (valueA valueB : Word)
    (counterA counterB : Nat) (tid : Fin 2) :
    Ownership.Disjoint ⟨(image compiler kind).base, (image compiler kind).bytes.length⟩
      (workerView compiler first second valueA valueB counterA counterB tid).resources.caller.loan.region := by
  rcases tid with ⟨tid, bound⟩
  have cases : tid = 0 ∨ tid = 1 := by omega
  rcases cases with rfl | rfl
  · change Ownership.Disjoint ⟨(image compiler kind).base, (image compiler kind).bytes.length⟩
      ⟨(0x700008 : Word), 8⟩
    cases compiler <;> cases kind <;> decide +kernel
  · change Ownership.Disjoint ⟨(image compiler kind).base, (image compiler kind).bytes.length⟩
      ⟨(0x710008 : Word), 8⟩
    cases compiler <;> cases kind <;> decide +kernel

/-- Actual useful finite inhabitants: arbitrary full64 RAM and both arguments,
arbitrary independent counters/occurrences, two private protected original
callers, and any homogeneous or mixed selection of the authenticated sites.
This inhabits independent Pre/ClosedPre without assuming a method or result. -/
def cohort (compiler : Compiler) (first second : Kind) (old valueA valueB : Word)
    (counterA counterB occurrenceA occurrenceB : Nat) :
    Cohort (programSpace compiler) (catalog compiler) standard old
      (choice compiler first valueA counterA occurrenceA) (choice compiler second valueB counterB occurrenceB) where
  resources := resources compiler first second old
  workerA := workerView compiler first second valueA valueB counterA counterB 0
  workerB := workerView compiler first second valueA valueB counterA counterB 1
  attached := ⟨started compiler first second old valueA valueB counterA counterB occurrenceA occurrenceB,
    checked_get _ (start_total compiler first second old valueA valueB counterA counterB occurrenceA occurrenceB),
    started_state compiler first second old valueA valueB counterA counterB occurrenceA occurrenceB⟩
  pre := by
    apply pre_pair
    · simpa only [started_state, state] using
        (started compiler first second old valueA valueB counterA counterB occurrenceA occurrenceB).valid
    · exact ⟨by simpa only [input_site, choice] using members compiler first,
        by simpa only [input_site, choice] using members compiler second⟩
    · exact entry compiler first second old valueA valueB counterA counterB occurrenceA occurrenceB 0
    · exact entry compiler first second old valueA valueB counterA counterB occurrenceA occurrenceB 1
    · exact private_callers compiler first second valueA valueB counterA counterB
    · simpa only [input_site, choice, site] using
        And.intro (code_caller compiler first first second valueA valueB counterA counterB 0)
          (And.intro (code_caller compiler first first second valueA valueB counterA counterB 1)
            (And.intro (code_caller compiler second first second valueA valueB counterA counterB 0)
              (code_caller compiler second first second valueA valueB counterA counterB 1)))
  counterA := rfl
  counterB := rfl
  emptyA := rfl
  emptyB := rfl
  protectedA := caller_protected compiler first second old valueA valueB counterA counterB 0
  protectedB := caller_protected compiler first second old valueA valueB counterA counterB 1

theorem pre (compiler : Compiler) (first second : Kind) (old valueA valueB : Word)
    (counterA counterB occurrenceA occurrenceB : Nat) :
    Plain64.Pre (catalog compiler)
      (cohort compiler first second old valueA valueB counterA counterB occurrenceA occurrenceB).state
      (cohort compiler first second old valueA valueB counterA counterB occurrenceA occurrenceB).inputs :=
  (cohort compiler first second old valueA valueB counterA counterB occurrenceA occurrenceB).pre

theorem closedPre (compiler : Compiler) (first second : Kind) (old valueA valueB : Word)
    (counterA counterB occurrenceA occurrenceB : Nat) :
    Plain64.ClosedPre (catalog compiler)
      (cohort compiler first second old valueA valueB counterA counterB occurrenceA occurrenceB).state
      (cohort compiler first second old valueA valueB counterA counterB occurrenceA occurrenceB).inputs :=
  (cohort compiler first second old valueA valueB counterA counterB occurrenceA occurrenceB).closedPre

end EDSL.Corpus.PlainResources.Frozen

#audit_edsl
