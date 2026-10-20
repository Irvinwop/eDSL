/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.ELF.CallerResources
import EDSL.PureCall.Domain

/-! Spec-indexed certificates for exact named function bytes in complete ELF
files. This module composes the existing production byte checker, sequential
semantics and current-resource providers. It supplies no interpreter, concrete
client or grading registration.

The callable target assumes stable ordinary RAM, four-level canonical addresses,
alignment checking disabled, CET/IBT and shadow stacks disabled, and no
asynchronous interference. OS principals, allocations and loans are modeled
authority supplied by the caller; native authority is not authenticated here.
Physical CPU/memory refinement, native loading/startup and source preservation
remain separate obligations.
-/

namespace EDSL.PureCall
open X86 X86.Sequential OS

/-- A present admitted call for an externally selected spec, complete file and
exact symbol name. All text and resource obligations use the same input bytes
and selected address. Admission has no result or future-execution premise.
Usefulness belongs to a certificate's existential witness, not every call. -/
structure ELFLoadedCall (spec : Spec) (file name : List Byte)
    (input : ELF.FunctionInput) where
  prior : AddressSpace.Space
  loaded : ELF.Loaded
  admitted : input.admit file name prior = .ok loaded
  resource : Resources spec
  initial : State
  pre : ResourcePre spec input.bytes resource initial
  entry : initial.rip = input.function.window.base
  text : ELF.FunctionWindow.TextUnchanged (AddressSpace.toMemory loaded.space)
    initial.memory input.function.window input.bytes.length

/-- Independent semantics for the checked bytes, jointly with a useful current
resource witness at the selected address of this exact complete file/name.
Arbitrary specs still require independent mathematical review. This type gives
no authority to replace a registered grading contract. -/
structure ELFCertificate (spec : Spec) (file name : List Byte) where
  input : ELF.FunctionInput
  checked : input.check file name = true
  semantics : Grading.ReadOnlySemanticClaim (readOnlyTask spec) input.bytes
  inhabited : ∃ call : ELFLoadedCall spec file name input,
    spec.useful call.resource.value

/-- The current executable bytes are at this call's actual selected address;
admission alone does not supply current text/execute-permission retention. -/
theorem ELFLoadedCall.code {spec : Spec} {file name : List Byte}
    {input : ELF.FunctionInput} (call : ELFLoadedCall spec file name input) :
    CodeAt call.initial.memory call.initial.rip input.bytes := by
  rw [call.entry]
  exact ELF.FunctionSymbol.admitted_current_code call.admitted call.text

/-- Convenience route through the neutral ELF installation and argument/resource
providers. Fresh LOAD pages preserve caller mappings. The resource providers
declare a NEW modeled ownership world; they do not infer or authenticate native
authority. All supplied admission facts describe current resources, text or
arguments. -/
def ELFCertificate.ofCaller (spec : Spec) {file name : List Byte}
    (input : ELF.FunctionInput) (checked : input.check file name = true)
    (semantics : Grading.ReadOnlySemanticClaim (readOnlyTask spec) input.bytes)
    (caller : ELF.CallerResources.Caller)
    (fresh : ELF.fresh input.table.image caller.prior = true)
    (callerFacts : caller.Facts)
    (separate : Ownership.Disjoint ⟨input.function.window.base, input.bytes.length⟩ caller.region)
    (value : spec.Input) (domain : spec.domain value) (useful : spec.useful value) :
    ELFCertificate spec file name := by
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

/-- Production checker binding for the same complete file, exact byte name,
selected interval and bytes that index the semantic claim. -/
theorem ELFCertificate.binding {spec : Spec} {file name : List Byte}
    (certificate : ELFCertificate spec file name) :
    ELF.FunctionSymbol.CheckedMetadata file certificate.input.table.header
      certificate.input.metadata ∧
    certificate.input.function.Contract certificate.input.metadata name
      certificate.input.bytes.length ∧
    ELF.FunctionWindow.Layout file certificate.input.table ∧
    ELF.FunctionWindow.Selection file certificate.input.table.image
      certificate.input.function.window certificate.input.bytes :=
  ELF.FunctionSymbol.checked_sound certificate.checked

/-- Every admitted current call has total execution for every AF stream,
the mathematical/ABI postcondition, retained original current resources at
return and the original resource read authority at every actual prefix.
There is no usefulness restriction on this universal call argument.

The production sequential x86 callable profile assumes stable ordinary RAM,
alignment checking disabled, four-level canonical addresses, CET/IBT and shadow
stacks disabled, supplied caller/loan authority and no asynchronous interference.
Ownership and OS principals are logical model facts, not authenticated native
authority. Native loading/startup, physical CPU/memory refinement, concurrent
interference control and source preservation are separate obligations. -/
theorem ELFCertificate.resource {spec : Spec} {file name : List Byte}
    (certificate : ELFCertificate spec file name)
    (call : ELFLoadedCall spec file name certificate.input) :
    AllExecutions call.initial (fun result =>
      Post spec (resourceInput call.resource) call.initial result.state ∧
      CallResources.Current call.resource.call call.resource.shared result.state) ∧
    Grading.ReadOnlyPolicy call.initial
      (CallResources.Current call.resource.call call.resource.shared)
      (fun _ read => CallResources.ReadAllowed call.resource.call call.resource.shared read) :=
  certificate.semantics.resource call.resource call.initial call.pre

/-- Both useful raw and current-resource domains follow from the same admitted
actual-address witness. A raw witness from another mapping cannot fill it. -/
theorem ELFCertificate.nonvacuous {spec : Spec} {file name : List Byte}
    (certificate : ELFCertificate spec file name) :
    Grading.ReadOnlyNonvacuous (readOnlyTask spec) certificate.input.bytes := by
  obtain ⟨call, useful⟩ := certificate.inhabited
  exact nonvacuous_of_resource call.resource call.initial useful call.pre

/-- Retain usefulness, actual-address executable code and the full universal
resource result together on the certificate's independently inhabited call. -/
theorem ELFCertificate.useful_execution {spec : Spec} {file name : List Byte}
    (certificate : ELFCertificate spec file name) :
    ∃ call : ELFLoadedCall spec file name certificate.input,
      spec.useful call.resource.value ∧
      CodeAt call.initial.memory call.initial.rip certificate.input.bytes ∧
      AllExecutions call.initial (fun result =>
        Post spec (resourceInput call.resource) call.initial result.state ∧
        CallResources.Current call.resource.call call.resource.shared result.state) ∧
      Grading.ReadOnlyPolicy call.initial
        (CallResources.Current call.resource.call call.resource.shared)
        (fun _ read => CallResources.ReadAllowed call.resource.call call.resource.shared read) := by
  obtain ⟨call, useful⟩ := certificate.inhabited
  exact ⟨call, useful, call.code, certificate.resource call⟩

end EDSL.PureCall
