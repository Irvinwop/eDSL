/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.Certificate
import EDSL.Grading.Registry
import EDSL.PureCall.ELFCertificateFor

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Corpus
open X86 X86.Sequential OS.AddressSpace

/-- Present file admission and current resources for a trusted execution/task
binding. A useful witness belongs to the certificate; universal semantic
correctness applies to every admitted resource, without a usefulness gate. -/
structure RegisteredLoadedCall (binding : Grading.RegisteredTask)
    (file name : List Byte) (input : FunctionInput) where
  prior : Space
  loaded : ELF.Loaded
  admitted : input.admit file name prior = .ok loaded
  resource : binding.task.Resource
  initial : State
  pre : binding.task.resourcePre input.bytes resource initial
  entry : initial.rip = input.function.window.base
  text : ELF.FunctionWindow.TextUnchanged (toMemory loaded.space) initial.memory
    input.function.window input.bytes.length

/-- This internal composition type accepts a fixed trusted binding. Public
registered certificates below obtain that binding only from the registry. -/
structure RegisteredCertificate (binding : Grading.RegisteredTask) (file name : List Byte) where
  input : FunctionInput
  checked : input.check file name = true
  claim : Grading.SemanticClaimFor binding.execution binding.task input.bytes ∧
    Grading.Nonvacuous binding.task input.bytes
  inhabited : ∃ call : RegisteredLoadedCall binding file name input,
    binding.task.useful (binding.task.input call.resource)

abbrev LoadedCallFor (id : Grading.RegistryID) := RegisteredLoadedCall (Grading.registry id)
abbrev CertificateFor (id : Grading.RegistryID) := RegisteredCertificate (Grading.registry id)

theorem RegisteredLoadedCall.code {binding : Grading.RegisteredTask} {file name : List Byte}
    {input : FunctionInput} (call : RegisteredLoadedCall binding file name input) :
    CodeAt call.initial.memory call.initial.rip input.bytes := by
  rw [call.entry]
  exact ELF.FunctionSymbol.admitted_current_code call.admitted call.text

theorem RegisteredCertificate.binding {binding : Grading.RegisteredTask} {file name : List Byte}
    (certificate : RegisteredCertificate binding file name) :
    ELF.FunctionSymbol.CheckedMetadata file certificate.input.table.header
      certificate.input.metadata ∧
    certificate.input.function.Contract certificate.input.metadata name
      certificate.input.bytes.length ∧
    ELF.FunctionWindow.Layout file certificate.input.table ∧
    ELF.FunctionWindow.Selection file certificate.input.table.image
      certificate.input.function.window certificate.input.bytes :=
  ELF.FunctionSymbol.checked_sound certificate.checked

theorem CertificateFor.registeredClaim {id : Grading.RegistryID} {file name : List Byte}
    (certificate : CertificateFor id file name) :
    Grading.RegisteredClaim id certificate.input.bytes := certificate.claim

/-- The complete postcondition, actual returned resource hook and every-prefix
policy use the executor and task fixed by trusted registration. Stable modeled
RAM, disabled CET/shadow stacks, supplied logical authority and absence of
asynchronous interference remain target assumptions. Native CPU/OS refinement,
loading/startup and source/compiler preservation are separate obligations. -/
theorem RegisteredCertificate.resource {binding : Grading.RegisteredTask} {file name : List Byte}
    (certificate : RegisteredCertificate binding file name)
    (call : RegisteredLoadedCall binding file name certificate.input) :
    Engine.AllExecutions binding.execution.transition call.initial (fun result =>
      binding.task.post (binding.task.input call.resource) call.initial result.state ∧
      binding.task.resourceReturn certificate.input.bytes call.resource call.initial result) ∧
    binding.task.resourcePolicy certificate.input.bytes call.resource call.initial :=
  certificate.claim.1.resource call.resource call.initial call.pre

/-- A shared adapter from a neutral read-only certificate retains the same
complete file/name/input and useful call at its selected actual address. -/
def RegisteredCertificate.ofReadOnly {model : ExecutionModel} {spec : PureCall.Spec}
    {file name : List Byte} (certificate : PureCall.ELFCertificateFor model spec file name) :
    RegisteredCertificate ⟨model, Grading.ofReadOnlyFor model (PureCall.readOnlyTask spec)⟩
      file name := by
  refine ⟨certificate.input, certificate.checked, ?_, ?_⟩
  · exact ⟨(Grading.ofReadOnlyFor_semanticClaim_iff model _ _).mpr certificate.semantics,
      (Grading.ofReadOnlyFor_nonvacuous_iff model _ _).mpr certificate.nonvacuous⟩
  · obtain ⟨call, useful⟩ := certificate.inhabited
    exact ⟨⟨call.prior, call.loaded, call.admitted, call.resource, call.initial,
      call.pre, call.entry, call.text⟩, useful⟩

/-- Bind the shared certificate adapter to a whole registry entry, rather than
letting a submission independently select a model, postcondition or policy. -/
def CertificateFor.ofReadOnly (id : Grading.RegistryID) (model : ExecutionModel)
    (spec : PureCall.Spec)
    (registration : Grading.registry id =
      ⟨model, Grading.ofReadOnlyFor model (PureCall.readOnlyTask spec)⟩)
    {file name : List Byte} (certificate : PureCall.ELFCertificateFor model spec file name) :
    CertificateFor id file name := by
  unfold CertificateFor
  rw [registration]
  exact RegisteredCertificate.ofReadOnly certificate

/-- Existing certificates keep their exact Bool execution, admission, policies,
actual resource-return hook and selected-address witness. -/
def CertificateFor.ofLegacy {id : Grading.TaskID} {file name : List Byte}
    (certificate : Certificate id file name) : CertificateFor (.legacy id) file name := by
  refine ⟨certificate.input, certificate.checked,
    ⟨Grading.SemanticClaimFor.ofBool certificate.claim.1, certificate.claim.2⟩, ?_⟩
  obtain ⟨call⟩ := certificate.inhabited
  exact ⟨⟨call.prior, call.loaded, call.admitted, call.resource, call.initial,
    call.pre, call.entry, call.text⟩, call.useful⟩

/-- Recover every original field of a legacy certificate. No conversion between
Bool and full-vector IMUL semantics is involved in either legacy adapter. -/
def CertificateFor.toLegacy {id : Grading.TaskID} {file name : List Byte}
    (certificate : CertificateFor (.legacy id) file name) : Certificate id file name := by
  refine ⟨certificate.input, certificate.checked,
    ⟨Grading.SemanticClaimFor.toBool certificate.claim.1, certificate.claim.2⟩, ?_⟩
  obtain ⟨call, useful⟩ := certificate.inhabited
  exact ⟨⟨call.prior, call.loaded, call.admitted, call.resource, call.initial,
    useful, call.pre, call.entry, call.text⟩⟩

end EDSL.Corpus
