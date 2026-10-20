/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.Certificate
import EDSL.Grading.BufferTask

set_option autoImplicit false
set_option warningAsError true

/-!
Exact final-ELF certificates for fixed registered buffer tasks. These are sibling
types of the scalar and concurrent certificates; no concrete program certificate
or score is supplied here. Universal body correctness and useful actual loaded
resources remain independent proof obligations.
-/

namespace EDSL.Corpus.Buffer
open X86 X86.Sequential OS.AddressSpace

/-- A useful present call at the actual checked function address. ResourcePre
binds complete current memory, code/input loans, the original caller slot and
ABI arguments. No candidate postcondition, decoder/checker, future execution or
desired result is admitted. Retention covers EVERY installed cell, including
nonfunction segments and all permissions, in that same current resource world.
The modeled ownership world does not authenticate native OS principals. -/
structure LoadedCall (id : Grading.BufferTask.TaskID) (file name : List Byte)
    (input : FunctionInput) where
  prior : Space
  loaded : ELF.Loaded
  admitted : input.admit file name prior = .ok loaded
  resource : BufferCall.Resources (Grading.BufferTask.registeredSpec id)
  initial : X86.State
  useful : (Grading.BufferTask.registeredSpec id).useful resource.value
  pre : BufferCall.ResourcePre (Grading.BufferTask.registeredSpec id)
    input.bytes resource initial
  entry : initial.rip = input.function.window.base
  text : ELF.FunctionWindow.TextUnchanged (toMemory loaded.space) initial.memory
    input.function.window input.bytes.length
  retainedImage : ∀ address original, loaded.space.cells address = some original →
    resource.shared.resources.space.cells address = some original

/-- The trusted task ID, complete file and requested name index the certificate.
FunctionInput.check authenticates the unique named complete function extent.
The claim is exactly the registered task for those checked bytes, and the useful
loaded domain belongs to this same file, function and actual address. -/
structure Certificate (id : Grading.BufferTask.TaskID) (file name : List Byte) where
  input : FunctionInput
  checked : input.check file name = true
  claim : Grading.BufferTask.Claim id input.bytes
  inhabited : Nonempty (LoadedCall id file name input)

theorem LoadedCall.code {id : Grading.BufferTask.TaskID} {file name : List Byte}
    {input : FunctionInput} (call : LoadedCall id file name input) :
    CodeAt call.initial.memory call.initial.rip input.bytes := by
  rw [call.entry]
  exact ELF.FunctionSymbol.admitted_current_code call.admitted call.text

/-- Package existing fixed-task semantics and useful loaded resources without
adding a body proof, running an alternate executor or choosing a candidate Spec.
Nonvacuity is derived from the very same current resources and initial state. -/
def Certificate.ofLoadedCall {id : Grading.BufferTask.TaskID} {file name : List Byte}
    (input : FunctionInput) (checked : input.check file name = true)
    (semantics : Grading.BufferTask.SemanticClaim id input.bytes)
    (call : LoadedCall id file name input) : Certificate id file name :=
  ⟨input, checked, ⟨semantics,
    BufferCall.nonvacuous_of_resource call.resource call.initial call.useful call.pre⟩, ⟨call⟩⟩

/-- Exact symbol metadata, the entire named extent and executable LOAD layout
follow from the same complete file supplied to the certificate. -/
theorem Certificate.binding {id : Grading.BufferTask.TaskID} {file name : List Byte}
    (certificate : Certificate id file name) :
    ELF.FunctionSymbol.CheckedMetadata file certificate.input.table.header
      certificate.input.metadata ∧
    certificate.input.function.Contract certificate.input.metadata name
      certificate.input.bytes.length ∧
    ELF.FunctionWindow.Layout file certificate.input.table ∧
    ELF.FunctionWindow.Selection file certificate.input.table.image
      certificate.input.function.window certificate.input.bytes :=
  ELF.FunctionSymbol.checked_sound certificate.checked

/-- Apply the same fixed claim to the actual loaded call for every AF stream.
The independent mathematical/ABI Post and current resources hold at return;
the existing read-only policy retains current authority at every prefix.
This composes the production executor's claim, with no new execution semantics.
The registered sequential callable profile's environmental assumptions apply. -/
theorem Certificate.resource {id : Grading.BufferTask.TaskID} {file name : List Byte}
    (certificate : Certificate id file name)
    (call : LoadedCall id file name certificate.input) :
    AllExecutions call.initial (fun result =>
      BufferCall.Post (Grading.BufferTask.registeredSpec id)
        (BufferCall.resourceInput call.resource) call.initial result.state ∧
      BufferCall.Current call.resource result.state) ∧
    Grading.ReadOnlyPolicy call.initial (BufferCall.Current call.resource)
      (fun _ read => BufferCall.ReadAllowed call.resource read) :=
  certificate.claim.1.resource call.resource call.initial call.pre

/-- Nonvacuity at this file's actual address, with total execution for arbitrary
AF choices and the independent registered result plus original current resources.
A useful witness at another address or for a weaker task cannot supply this. -/
theorem Certificate.useful_execution {id : Grading.BufferTask.TaskID} {file name : List Byte}
    (certificate : Certificate id file name) :
    ∃ call : LoadedCall id file name certificate.input,
      CodeAt call.initial.memory call.initial.rip certificate.input.bytes ∧
      AllExecutions call.initial (fun result =>
        BufferCall.Post (Grading.BufferTask.registeredSpec id)
          (BufferCall.resourceInput call.resource) call.initial result.state ∧
        BufferCall.Current call.resource result.state) := by
  obtain ⟨call⟩ := certificate.inhabited
  exact ⟨call, call.code, (certificate.resource call).1⟩

end EDSL.Corpus.Buffer
