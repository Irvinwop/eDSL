/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.ELF.FunctionInput
import EDSL.Grading.Task

namespace EDSL.Corpus
open X86 X86.Sequential OS.AddressSpace

/-- Compatibility name for the neutral named-function input. Registered
certificates retain their independently fixed task contracts below. -/
abbrev FunctionInput := ELF.FunctionInput

abbrev FunctionInput.mk := ELF.FunctionInput.mk
abbrev FunctionInput.table (input : FunctionInput) := ELF.FunctionInput.table input
abbrev FunctionInput.metadata (input : FunctionInput) := ELF.FunctionInput.metadata input
abbrev FunctionInput.function (input : FunctionInput) := ELF.FunctionInput.function input
abbrev FunctionInput.bytes (input : FunctionInput) := ELF.FunctionInput.bytes input
abbrev FunctionInput.checkWith (maxBytes : Nat) (input : FunctionInput) (file name : List Byte) : Bool :=
  ELF.FunctionInput.checkWith maxBytes input file name
abbrev FunctionInput.admitWith (maxBytes : Nat) (input : FunctionInput) (file name : List Byte)
    (prior : Space) : Except ELF.Error ELF.Loaded :=
  ELF.FunctionInput.admitWith maxBytes input file name prior
abbrev FunctionInput.check (input : FunctionInput) (file name : List Byte) : Bool :=
  ELF.FunctionInput.check input file name
abbrev FunctionInput.admit (input : FunctionInput) (file name : List Byte) (prior : Space) :
    Except ELF.Error ELF.Loaded :=
  FunctionInput.admitWith 64 input file name prior

namespace FunctionInput
export ELF.FunctionInput (rec recOn casesOn noConfusionType noConfusion ctorIdx)
namespace mk
export ELF.FunctionInput.mk (inj injEq noConfusion sizeOf_spec)
end mk
end FunctionInput

/-- A useful, actually inhabited callable domain at the selected file address.
All environmental authority is supplied by the registered resource admission.
The constructor does not infer native ownership from a readable mapping, and
requires neither execution nor a desired result in its input fields. -/
structure LoadedCall (id : Grading.TaskID) (file name : List Byte) (input : FunctionInput) where
  prior : Space
  loaded : ELF.Loaded
  admitted : input.admit file name prior = .ok loaded
  resource : (Grading.registered id).Resource
  initial : X86.State
  useful : (Grading.registered id).useful ((Grading.registered id).input resource)
  pre : (Grading.registered id).resourcePre input.bytes resource initial
  entry : initial.rip = input.function.window.base
  text : ELF.FunctionWindow.TextUnchanged (toMemory loaded.space) initial.memory
    input.function.window input.bytes.length

/-- File/name binding, independent registered semantics, and useful resource
nonvacuity at the actual selected address are joint obligations. An old witness
at another address cannot supply the final field. No IO extractor, hash or
native test supplies a proof field here. -/
structure Certificate (id : Grading.TaskID) (file name : List Byte) where
  input : FunctionInput
  checked : input.check file name = true
  claim : Grading.Claim id input.bytes
  inhabited : Nonempty (LoadedCall id file name input)

theorem LoadedCall.code {id : Grading.TaskID} {file name : List Byte}
    {input : FunctionInput} (call : LoadedCall id file name input) :
    CodeAt call.initial.memory call.initial.rip input.bytes := by
  rw [call.entry]
  exact ELF.FunctionSymbol.admitted_current_code call.admitted call.text

/-- The exact symbol metadata, source interval and executable LOAD layout
follow from the same literal complete-file input used by the certificate. -/
theorem Certificate.binding {id : Grading.TaskID} {file name : List Byte}
    (certificate : Certificate id file name) :
    ELF.FunctionSymbol.CheckedMetadata file certificate.input.table.header
      certificate.input.metadata ∧
    certificate.input.function.Contract certificate.input.metadata name
      certificate.input.bytes.length ∧
    ELF.FunctionWindow.Layout file certificate.input.table ∧
    ELF.FunctionWindow.Selection file certificate.input.table.image
      certificate.input.function.window certificate.input.bytes :=
  ELF.FunctionSymbol.checked_sound certificate.checked

/-- Every admitted current-resource call, at the selected address with its
checked installed text retained, has the registered result, actual return hook and
every-prefix policy for every AF stream. This theorem composes existing proved
rules; it supplies no per-program step proof or weaker admission predicate.

Current memory comes from the registered environment; the selected text's
bytes and execute permission must persist from the checked installation.
The target machine, stable modeled RAM, caller/ownership authority and absent
asynchronous interference remain the registered profile's explicit environment.
This does not establish native Linux startup, physical CPU refinement or source
preservation. -/
theorem Certificate.resource {id : Grading.TaskID} {file name : List Byte}
    (certificate : Certificate id file name)
    (call : LoadedCall id file name certificate.input) :
    AllExecutions call.initial (fun result =>
      (Grading.registered id).post ((Grading.registered id).input call.resource)
        call.initial result.state ∧
      (Grading.registered id).resourceReturn certificate.input.bytes
        call.resource call.initial result) ∧
    (Grading.registered id).resourcePolicy certificate.input.bytes call.resource call.initial :=
  certificate.claim.1.resource call.resource call.initial call.pre

/-- The full result applies to an independently useful actual-address domain;
nonvacuity is not borrowed from a different file or callable mapping. -/
theorem Certificate.useful_execution {id : Grading.TaskID} {file name : List Byte}
    (certificate : Certificate id file name) :
    ∃ call : LoadedCall id file name certificate.input,
      CodeAt call.initial.memory call.initial.rip certificate.input.bytes ∧
      AllExecutions call.initial (fun result =>
        (Grading.registered id).post ((Grading.registered id).input call.resource)
          call.initial result.state ∧
        (Grading.registered id).resourceReturn certificate.input.bytes
          call.resource call.initial result) := by
  obtain ⟨call⟩ := certificate.inhabited
  exact ⟨call, call.code, (certificate.resource call).1⟩

end EDSL.Corpus
