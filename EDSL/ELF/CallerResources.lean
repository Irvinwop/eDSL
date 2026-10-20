/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.ELF.FunctionInput
import EDSL.OS.CallResources.Domain

namespace EDSL.ELF.CallerResources
open X86 OS OS.AddressSpace

/-- Caller mappings and proof-level principals supplied before fresh image
installation. These declarations do not authenticate native OS authority. -/
structure Caller where
  prior : Space
  codeOwner : Nat
  callerOwner : Nat
  worker : Nat
  stack : Word
  returnAddress : Word

def Caller.region (caller : Caller) : Region := ⟨caller.stack, 8⟩

/-- Present caller facts, independent of file bytes, decoding and results. -/
structure Caller.Facts (caller : Caller) : Prop where
  valid : caller.region.valid = true
  readable : Borrowing.allReadable caller.prior caller.region = true
  stack : readWord (toMemory caller.prior) caller.stack = .ok caller.returnAddress
  returnCanonical : canonical caller.returnAddress = true
  stackBound : caller.stack.toNat + 8 < 2^64
  postStackCanonical : canonical (caller.stack + 8) = true

def loaded (file : List Byte) (input : FunctionInput) (caller : Caller) : ELF.Loaded :=
  ⟨input.table.image, ELF.install file input.table.image caller.prior⟩

def initial (file : List Byte) (input : FunctionInput) (caller : Caller) :
    CallResources.Domain.Initial where
  space := (loaded file input caller).space
  codeOwner := caller.codeOwner
  callerOwner := caller.callerOwner
  worker := caller.worker
  code := input.function.window.base
  bytes := input.bytes
  stack := caller.stack
  returnAddress := caller.returnAddress

/-- This helper only packages the existing named-file and freshness checks. -/
theorem admitted {file name : List Byte} {input : FunctionInput} {caller : Caller}
    (checked : input.check file name = true)
    (fresh : ELF.fresh input.table.image caller.prior = true) :
    input.admit file name caller.prior = .ok (loaded file input caller) := by
  have named : ELF.FunctionSymbol.check file input.table input.metadata name
      input.function input.bytes = true := checked
  have window : ELF.FunctionWindow.check file input.table input.function.window input.bytes = true := by
    have parts := named
    simp only [ELF.FunctionSymbol.check, Bool.and_eq_true] at parts
    exact parts.2
  simp only [FunctionInput.admit, ELF.FunctionSymbol.admit, named, ELF.FunctionWindow.admit,
    window, fresh, loaded, ↓reduceIte]

/-- Every readable prior stack cell survives fresh installation, including its
permissions. This theorem transports present data rather than reevaluating a
large literal image at each stack byte. -/
theorem stack_cells {file name : List Byte} {input : FunctionInput} {caller : Caller}
    (checked : input.check file name = true)
    (fresh : ELF.fresh input.table.image caller.prior = true)
    (facts : caller.Facts) (address : Word) (inside : caller.region.Contains address) :
    ∃ cell, (loaded file input caller).space.cells address = some cell ∧
      caller.prior.cells address = some cell ∧ cell.permissions.readable = true := by
  obtain ⟨cell, found, readable⟩ := Borrowing.allReadable_inside _ _ facts.readable address inside
  have keep := (ELF.FunctionSymbol.admitted_sound (admitted checked fresh)).2.2.2.2.2
  exact ⟨cell, keep address cell found, found, readable⟩

theorem stack_agrees {file name : List Byte} {input : FunctionInput} {caller : Caller}
    (checked : input.check file name = true)
    (fresh : ELF.fresh input.table.image caller.prior = true) (facts : caller.Facts) :
    MemoryAgreesOn (toMemory (loaded file input caller).space) (toMemory caller.prior)
      caller.stack 8 := by
  intro offset bound
  have extent : caller.stack.toNat + 8 ≤ 2^64 := by have := facts.stackBound; omega
  have small : offset < 2^64 := by omega
  have total : caller.stack.toNat + offset < 2^64 := by omega
  have inside : caller.region.Contains (caller.stack + BitVec.ofNat 64 offset) := by
    simp only [Caller.region, Region.Contains, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt total]
    omega
  obtain ⟨cell, now, prior, _⟩ := stack_cells checked fresh facts _ inside
  simp only [toMemory, now, prior]

/-- Generic actual-address resource witness. The caller/code interval separation
is explicit. Authority is the existing NEW modeled initial registry, with no
preexisting/native loans inferred or transported. -/
theorem initial_facts {file name : List Byte} {input : FunctionInput} {caller : Caller}
    (checked : input.check file name = true)
    (fresh : ELF.fresh input.table.image caller.prior = true) (facts : caller.Facts)
    (separate : Ownership.Disjoint ⟨input.function.window.base, input.bytes.length⟩ caller.region) :
    CallResources.Domain.Facts (initial file input caller) := by
  have sound := ELF.FunctionSymbol.admitted_sound (admitted checked fresh)
  have bounds := sound.2.2.2.1.bounds
  have code := sound.2.2.2.2.1
  have addressBound : input.function.window.address < 2^64 := by
    have := bounds.2.2.1
    omega
  have codeValid : (⟨input.function.window.base, input.bytes.length⟩ : Region).valid = true := by
    simp only [Region.valid, ELF.FunctionWindow.Window.base,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt addressBound, decide_eq_true_eq]
    exact ⟨bounds.1, by have := bounds.2.2.1; omega, Or.inl bounds.2.2.1⟩
  refine ⟨codeValid, facts.valid, separate, CallResources.Domain.code_readable _ _ _ code,
    ?_, code, ?_, facts.returnCanonical, facts.stackBound, facts.postStackCanonical⟩
  · apply CallResources.Domain.allReadable_of_cells _ _ facts.valid
    intro address inside
    obtain ⟨cell, now, _, readable⟩ := stack_cells checked fresh facts address inside
    exact ⟨cell, now, readable⟩
  · exact (readWord_congr _ _ _ (stack_agrees checked fresh facts)).trans facts.stack

end EDSL.ELF.CallerResources
