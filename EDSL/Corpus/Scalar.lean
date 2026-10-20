/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.ELFResources
import EDSL.PureCall.Domain
import EDSL.PureCall.ELFCertificate

namespace EDSL.Corpus.Scalar
open X86 OS

/-- Compatibility names for the neutral scalar argument/resource domain. -/
abbrev argumentValue := PureCall.Domain.argumentValue

theorem argumentValue_holds (argument : PureCall.Argument) :
    argument.Holds (argumentValue (some argument)) :=
  PureCall.Domain.argumentValue_holds argument

abbrev registers := PureCall.Domain.registers
abbrev initial := PureCall.Domain.initial

theorem initial_arguments (environment : CallResources.Domain.Initial)
    (spec : PureCall.Spec) (value : spec.Input) :
    PureCall.Bound spec value (initial environment spec value) :=
  PureCall.Domain.initial_arguments environment spec value

abbrev resource := PureCall.Domain.resource

theorem resource_pre {environment : CallResources.Domain.Initial}
    (facts : CallResources.Domain.Facts environment) (spec : PureCall.Spec)
    (value : spec.Input) {bytes : List Byte} (source : environment.bytes = bytes)
    (domain : spec.domain value) :
    PureCall.ResourcePre spec bytes (resource environment spec value)
      (initial environment spec value) :=
  PureCall.Domain.resource_pre facts spec value source domain

/-- Registration fixes the entire mathematical contract. Equality with the
registered task is a kernel proof obligation; a candidate cannot select a
weaker spec. All remaining inputs describe present admitted resources/text. -/
theorem loadedCall (id : Grading.TaskID) (spec : PureCall.Spec)
    (registration : Grading.registered id = Grading.ofReadOnly (PureCall.readOnlyTask spec))
    {file name : List Byte} (input : FunctionInput)
    (prior : AddressSpace.Space) (loaded : ELF.Loaded)
    (admitted : input.admit file name prior = .ok loaded)
    (currentResource : PureCall.Resources spec) (machine : State)
    (useful : spec.useful currentResource.value)
    (pre : PureCall.ResourcePre spec input.bytes currentResource machine)
    (entry : machine.rip = input.function.window.base)
    (text : ELF.FunctionWindow.TextUnchanged (AddressSpace.toMemory loaded.space)
      machine.memory input.function.window input.bytes.length) :
    Nonempty (LoadedCall id file name input) := by
  have present : ∃ current : (Grading.registered id).Resource,
      (Grading.registered id).useful ((Grading.registered id).input current) ∧
      (Grading.registered id).resourcePre input.bytes current machine := by
    rw [registration]
    exact ⟨currentResource, useful, pre⟩
  obtain ⟨current, usefulCurrent, presentCurrent⟩ := present
  exact ⟨⟨prior, loaded, admitted, current, machine, usefulCurrent,
    presentCurrent, entry, text⟩⟩

/-- Shared final-file constructor for registry-owned scalar tasks. Fresh ELF
installation transports supplied caller mappings; current loans inhabit a NEW
declared model world. This does not infer native authority. Independent math,
exact complete-file/name checking, caller facts and separation remain required.
There is no per-function interpreter, step proof or future-run admission. -/
def certificate (id : Grading.TaskID) (spec : PureCall.Spec)
    (registration : Grading.registered id = Grading.ofReadOnly (PureCall.readOnlyTask spec))
    {file name : List Byte} (input : FunctionInput)
    (checked : input.check file name = true)
    (semantics : Grading.ReadOnlySemanticClaim (PureCall.readOnlyTask spec) input.bytes)
    (caller : ELFResources.Caller)
    (fresh : ELF.fresh input.table.image caller.prior = true)
    (callerFacts : caller.Facts)
    (separate : Ownership.Disjoint ⟨input.function.window.base, input.bytes.length⟩ caller.region)
    (value : spec.Input) (domain : spec.domain value) (useful : spec.useful value) :
    Certificate id file name := by
  let standalone := PureCall.ELFCertificate.ofCaller spec input checked semantics
    caller fresh callerFacts separate value domain useful
  have claim : Grading.Claim id input.bytes := by
    unfold Grading.Claim
    rw [registration]
    exact (Grading.old_claim_iff (PureCall.readOnlyTask spec) input.bytes).mpr
      ⟨standalone.semantics, standalone.nonvacuous⟩
  refine ⟨input, checked, claim, ?_⟩
  obtain ⟨call, usefulCall⟩ := standalone.inhabited
  exact loadedCall id spec registration input call.prior call.loaded call.admitted
    call.resource call.initial usefulCall call.pre call.entry call.text

end EDSL.Corpus.Scalar
