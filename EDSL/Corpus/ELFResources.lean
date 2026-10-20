/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.Certificate
import EDSL.ELF.CallerResources

namespace EDSL.Corpus.ELFResources
open X86 OS OS.AddressSpace

/-- Compatibility names for the neutral present caller-resource provider. -/
abbrev Caller := ELF.CallerResources.Caller
abbrev Caller.mk := ELF.CallerResources.Caller.mk
abbrev Caller.prior (caller : Caller) := ELF.CallerResources.Caller.prior caller
abbrev Caller.codeOwner (caller : Caller) := ELF.CallerResources.Caller.codeOwner caller
abbrev Caller.callerOwner (caller : Caller) := ELF.CallerResources.Caller.callerOwner caller
abbrev Caller.worker (caller : Caller) := ELF.CallerResources.Caller.worker caller
abbrev Caller.stack (caller : Caller) := ELF.CallerResources.Caller.stack caller
abbrev Caller.returnAddress (caller : Caller) := ELF.CallerResources.Caller.returnAddress caller
abbrev Caller.region (caller : Caller) := ELF.CallerResources.Caller.region caller
abbrev Caller.Facts (caller : Caller) : Prop := ELF.CallerResources.Caller.Facts caller
abbrev Caller.Facts.mk := @ELF.CallerResources.Caller.Facts.mk
abbrev Caller.Facts.valid {caller : Caller} (facts : caller.Facts) :=
  ELF.CallerResources.Caller.Facts.valid facts
abbrev Caller.Facts.readable {caller : Caller} (facts : caller.Facts) :=
  ELF.CallerResources.Caller.Facts.readable facts
abbrev Caller.Facts.stack {caller : Caller} (facts : caller.Facts) :=
  ELF.CallerResources.Caller.Facts.stack facts
abbrev Caller.Facts.returnCanonical {caller : Caller} (facts : caller.Facts) :=
  ELF.CallerResources.Caller.Facts.returnCanonical facts
abbrev Caller.Facts.stackBound {caller : Caller} (facts : caller.Facts) :=
  ELF.CallerResources.Caller.Facts.stackBound facts
abbrev Caller.Facts.postStackCanonical {caller : Caller} (facts : caller.Facts) :=
  ELF.CallerResources.Caller.Facts.postStackCanonical facts

namespace Caller
export ELF.CallerResources.Caller (rec recOn casesOn noConfusionType noConfusion ctorIdx)
namespace mk
export ELF.CallerResources.Caller.mk (inj injEq noConfusion sizeOf_spec)
end mk
namespace Facts
export ELF.CallerResources.Caller.Facts (rec recOn casesOn)
end Facts
end Caller

abbrev loaded := ELF.CallerResources.loaded
abbrev initial := ELF.CallerResources.initial

theorem admitted {file name : List Byte} {input : FunctionInput} {caller : Caller}
    (checked : input.check file name = true)
    (fresh : ELF.fresh input.table.image caller.prior = true) :
    input.admit file name caller.prior = .ok (loaded file input caller) :=
  ELF.CallerResources.admitted checked fresh

theorem stack_cells {file name : List Byte} {input : FunctionInput} {caller : Caller}
    (checked : input.check file name = true)
    (fresh : ELF.fresh input.table.image caller.prior = true)
    (facts : caller.Facts) (address : Word) (inside : caller.region.Contains address) :
    ∃ cell, (loaded file input caller).space.cells address = some cell ∧
      caller.prior.cells address = some cell ∧ cell.permissions.readable = true :=
  ELF.CallerResources.stack_cells checked fresh facts address inside

theorem stack_agrees {file name : List Byte} {input : FunctionInput} {caller : Caller}
    (checked : input.check file name = true)
    (fresh : ELF.fresh input.table.image caller.prior = true) (facts : caller.Facts) :
    MemoryAgreesOn (toMemory (loaded file input caller).space) (toMemory caller.prior)
      caller.stack 8 :=
  ELF.CallerResources.stack_agrees checked fresh facts

theorem initial_facts {file name : List Byte} {input : FunctionInput} {caller : Caller}
    (checked : input.check file name = true)
    (fresh : ELF.fresh input.table.image caller.prior = true) (facts : caller.Facts)
    (separate : Ownership.Disjoint ⟨input.function.window.base, input.bytes.length⟩ caller.region) :
    CallResources.Domain.Facts (initial file input caller) :=
  ELF.CallerResources.initial_facts checked fresh facts separate

end EDSL.Corpus.ELFResources
