/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.ELF.FunctionInput
import EDSL.Grading.ConcurrentTask.Plain64.Admission

/-!
Exact named-file inputs and present loaded resources for managed plain64 calls.
The registry fixes the load/store interface and symbol names. A candidate
supplies a checked whole-file function selection, never its own mathematics.
These bindings alone supply no behavioral certificate or corpus credit.
-/

set_option autoImplicit false

namespace EDSL.Corpus.Plain
open X86 OS Grading.ConcurrentTask.Plain64

/-- Registry names are exact ELF byte names, without the terminating NUL. -/
def name : Kind → List Byte
  | .loadAcquire => [99,95,97,116,111,109,105,99,95,108,111,97,100,95,97,99,113,117,105,114,101,54,52]
  | .storeRelease => [99,95,97,116,111,109,105,99,95,115,116,111,114,101,95,114,101,108,101,97,115,101,54,52]

/-- Corpus definition IDs are distinct from ELF symbol-table row indices. -/
def definitionID : Kind → Nat
  | .loadAcquire => 35
  | .storeRelease => 36

structure NamedImage (file : List Byte) where
  kind : Kind
  input : ELF.FunctionInput
  checked : input.check file (name kind) = true

def NamedImage.site {file : List Byte} (named : NamedImage file) : Site :=
  ⟨named.kind, ⟨named.input.function.window.base, named.input.bytes⟩⟩

/-- Actual current resources over the entire loaded image. The separate useful
execution/certificate must inhabit this provider; a type alone establishes none.
All selected images are admitted against the same full file and prior space.
Targets are fresh from every loaded image cell, not merely from code bytes. -/
structure LoadedBatch (file : List Byte) (named : List (NamedImage file)) where
  priorSpace : AddressSpace.Space
  loaded : ELF.Loaded
  admitted : ∀ selected ∈ named,
    selected.input.admit file (name selected.kind) priorSpace = .ok loaded
  before : TSO64.State
  inputs : Fin before.workers.length → Input
  pre : ClosedPre (named.map NamedImage.site) before inputs
  text : ∀ selected ∈ named,
    ELF.FunctionWindow.TextUnchanged (AddressSpace.toMemory loaded.space)
      (TSO64.published before.world) selected.input.function.window selected.input.bytes.length
  retainedImage : ∀ address original, loaded.space.cells address = some original →
    before.world.legacy.shared.resources.space.cells address = some original
  targetsFresh : ∀ tid address original, loaded.space.cells address = some original →
    ¬ (AddressSpace.qwordRegion (inputs tid).cell.address).Contains address

/-- Checked named selection and present text preservation bind the entire
selected machine-code window to the same independently admitted loaded batch. -/
theorem LoadedBatch.code {file : List Byte} {named : List (NamedImage file)}
    (batch : LoadedBatch file named) {selected : NamedImage file}
    (member : selected ∈ named) :
    CodeAt (TSO64.published batch.before.world) selected.input.function.window.base selected.input.bytes :=
  ELF.FunctionSymbol.admitted_current_code (batch.admitted selected member) (batch.text selected member)

end EDSL.Corpus.Plain

#audit_edsl
