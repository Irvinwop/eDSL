/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.PureCall.ELFCertificate
import EDSL.PureCall.ResourcesFor
import EDSL.Grading.ReadOnlyClaimFor

set_option autoImplicit false
set_option warningAsError true

/-! Execution-indexed neutral certificates for exact named function bytes in
complete ELF files. The existing model-independent `ELFLoadedCall` supplies
admission, current resources, the selected actual entry and text retention.
Only the semantic claim and its execution/policy conclusions select a model.

The callable target assumes stable ordinary RAM, four-level canonical addresses,
alignment checking disabled, CET/IBT and shadow stacks disabled, supplied logical
caller/loan authority and no asynchronous interference. Native OS authority,
loading/startup, physical CPU/memory correspondence and compiler/source
preservation remain separate obligations. Arbitrary specs require independent
mathematical review and cannot replace a registered task.
-/

namespace EDSL.PureCall
open X86 X86.Sequential OS

/-- Independent selected-model semantics for the checked bytes, together with
a useful present call at this exact file/name's selected address. The call is
the unchanged `ELFLoadedCall`; admission adds no future-execution premise. -/
structure ELFCertificateFor (model : ExecutionModel) (spec : Spec)
    (file name : List Byte) where
  input : ELF.FunctionInput
  checked : input.check file name = true
  semantics : Grading.ReadOnlySemanticClaimFor model (readOnlyTask spec) input.bytes
  inhabited : ∃ call : ELFLoadedCall spec file name input,
    spec.useful call.resource.value

/-- Reuse the neutral ELF installation and original caller/resource providers.
Fresh LOAD pages preserve prior mappings. The supplied facts and separation
establish present resources, arguments and current text at the selected entry.
The providers declare a new logical ownership world, without authenticating
native authority or requiring a successful future run. -/
def ELFCertificateFor.ofCaller (model : ExecutionModel) (spec : Spec)
    {file name : List Byte}
    (input : ELF.FunctionInput) (checked : input.check file name = true)
    (semantics : Grading.ReadOnlySemanticClaimFor model (readOnlyTask spec) input.bytes)
    (caller : ELF.CallerResources.Caller)
    (fresh : ELF.fresh input.table.image caller.prior = true)
    (callerFacts : caller.Facts)
    (separate : Ownership.Disjoint ⟨input.function.window.base, input.bytes.length⟩ caller.region)
    (value : spec.Input) (domain : spec.domain value) (useful : spec.useful value) :
    ELFCertificateFor model spec file name := by
  let environment := ELF.CallerResources.initial file input caller
  have facts : CallResources.Domain.Facts environment :=
    ELF.CallerResources.initial_facts checked fresh callerFacts separate
  have pre := Domain.resource_pre facts spec value rfl domain
  have text : ELF.FunctionWindow.TextUnchanged
      (AddressSpace.toMemory (ELF.CallerResources.loaded file input caller).space)
      (Domain.initial environment spec value).memory input.function.window
      input.bytes.length := by
    intro _ _
    exact ⟨rfl, rfl⟩
  refine ⟨input, checked, semantics, ?_⟩
  exact ⟨⟨caller.prior, ELF.CallerResources.loaded file input caller,
    ELF.CallerResources.admitted checked fresh,
    Domain.resource environment spec value,
    Domain.initial environment spec value, pre, rfl, text⟩, useful⟩

/-- The unchanged production checker binds the complete file, exact byte name,
metadata, layout, selected interval and bytes indexing the semantic claim. -/
theorem ELFCertificateFor.binding {model : ExecutionModel} {spec : Spec}
    {file name : List Byte} (certificate : ELFCertificateFor model spec file name) :
    ELF.FunctionSymbol.CheckedMetadata file certificate.input.table.header
      certificate.input.metadata ∧
    certificate.input.function.Contract certificate.input.metadata name
      certificate.input.bytes.length ∧
    ELF.FunctionWindow.Layout file certificate.input.table ∧
    ELF.FunctionWindow.Selection file certificate.input.table.image
      certificate.input.function.window certificate.input.bytes :=
  ELF.FunctionSymbol.checked_sound certificate.checked

/-- Every admitted current call retains the complete mathematical/ABI result,
current resources at return and the original read authority at every actual
continuing prefix, for every choice stream of the selected production model.
Usefulness does not restrict this universal call argument.

Stable ordinary RAM, four-level canonical addresses, alignment checking off,
CET/IBT and shadow stacks off, supplied logical caller/loan authority and no
asynchronous interference are target assumptions. Native OS/CPU correspondence,
loading/startup and compiler/source preservation are separate obligations. -/
theorem ELFCertificateFor.resource {model : ExecutionModel} {spec : Spec}
    {file name : List Byte} (certificate : ELFCertificateFor model spec file name)
    (call : ELFLoadedCall spec file name certificate.input) :
    Engine.AllExecutions model.transition call.initial (fun result =>
      Post spec (resourceInput call.resource) call.initial result.state ∧
      CallResources.Current call.resource.call call.resource.shared result.state) ∧
    Grading.ReadOnlyPolicyFor model call.initial
      (CallResources.Current call.resource.call call.resource.shared)
      (fun _ read => CallResources.ReadAllowed call.resource.call call.resource.shared read) :=
  certificate.semantics.resource call.resource call.initial call.pre

/-- Both original useful raw and current-resource domains use the same
independently inhabited admitted call at the selected actual address. -/
theorem ELFCertificateFor.nonvacuous {model : ExecutionModel} {spec : Spec}
    {file name : List Byte} (certificate : ELFCertificateFor model spec file name) :
    Grading.ReadOnlyNonvacuous (readOnlyTask spec) certificate.input.bytes := by
  obtain ⟨call, useful⟩ := certificate.inhabited
  exact nonvacuous_of_resource call.resource call.initial useful call.pre

/-- Keep the useful actual-address call, its current executable code and the
full universal resource result/policy together in one witness. -/
theorem ELFCertificateFor.useful_execution {model : ExecutionModel} {spec : Spec}
    {file name : List Byte} (certificate : ELFCertificateFor model spec file name) :
    ∃ call : ELFLoadedCall spec file name certificate.input,
      spec.useful call.resource.value ∧
      CodeAt call.initial.memory call.initial.rip certificate.input.bytes ∧
      Engine.AllExecutions model.transition call.initial (fun result =>
        Post spec (resourceInput call.resource) call.initial result.state ∧
        CallResources.Current call.resource.call call.resource.shared result.state) ∧
      Grading.ReadOnlyPolicyFor model call.initial
        (CallResources.Current call.resource.call call.resource.shared)
        (fun _ read => CallResources.ReadAllowed call.resource.call call.resource.shared read) := by
  obtain ⟨call, useful⟩ := certificate.inhabited
  exact ⟨call, useful, call.code, certificate.resource call⟩

/-- Bool compatibility retains the exact input, full-file/name check and
inhabited call, converting both complete semantic domains without weakening. -/
def ELFCertificateFor.ofBool {spec : Spec} {file name : List Byte}
    (certificate : ELFCertificate spec file name) :
    ELFCertificateFor .bool spec file name :=
  ⟨certificate.input, certificate.checked,
    Grading.ReadOnlySemanticClaimFor.ofBool certificate.semantics, certificate.inhabited⟩

/-- Recover the original Bool certificate with the same selected bytes and
admitted useful call. No cross-model fallback is supplied. -/
def ELFCertificateFor.toBool {spec : Spec} {file name : List Byte}
    (certificate : ELFCertificateFor .bool spec file name) :
    ELFCertificate spec file name :=
  ⟨certificate.input, certificate.checked,
    Grading.ReadOnlySemanticClaimFor.toBool certificate.semantics, certificate.inhabited⟩

end EDSL.PureCall
