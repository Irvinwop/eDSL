/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Examples.Verification.DoubleELF
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.ELFCertificate
open X86 X86.Sequential OS PureCall
open Examples.Verification.Double
open Examples.Verification.DoubleELF

-- Header/table/name-shape coverage stays in ELFFunctionSymbol. These clients
-- exercise the final-file, selected-address and current-resource composition.

/-- The different routine at the ELF entry cannot authenticate Double. The
positive complete-file and non-entry symbol checks are `checked`/`admitted`. -/
theorem entry_is_not_double : ELF.checkEntry file table.image bytes = false := by decide +kernel

private theorem rejected_admit (candidate : ELF.FunctionInput) (requested : List Byte)
    (rejected : candidate.check file requested = false) :
    candidate.admit file requested caller.prior = .error .invalidImage := by
  have failed : ELF.FunctionSymbol.check file candidate.table candidate.metadata requested
      candidate.function candidate.bytes = false := rejected
  simp only [ELF.FunctionInput.admit, ELF.FunctionSymbol.admit, failed,
    Bool.false_eq_true, ↓reduceIte]

/-- The genuine other symbol name is not the selected function's name. -/
theorem wrong_name_rejected :
    input.check file [0x68, 0x65, 0x6c, 0x70, 0x65, 0x72] = false ∧
    input.admit file [0x68, 0x65, 0x6c, 0x70, 0x65, 0x72] caller.prior =
      .error .invalidImage := by
  have rejected : input.check file [0x68, 0x65, 0x6c, 0x70, 0x65, 0x72] = false :=
    by decide +kernel
  exact ⟨rejected, rejected_admit _ _ rejected⟩

def wrongBytes : ELF.FunctionInput :=
  { input with bytes := [0x48, 0x8d, 0x04, 0x37, 0xc3] }

/-- The same-length RDI+RSI variant cannot borrow the RDI+RDI proof merely
because file, name, declared extent and instruction count still agree. -/
theorem wrong_bytes_rejected : wrongBytes.check file name = false ∧
    wrongBytes.admit file name caller.prior = .error .invalidImage := by
  have rejected : wrongBytes.check file name = false := by decide +kernel
  exact ⟨rejected, rejected_admit _ _ rejected⟩

def shortExtent : ELF.FunctionInput := { input with bytes := [0x48, 0x8d, 0x04, 0x3f] }

/-- An authentic executable prefix passes the window checker but cannot be
admitted as the complete named function: the real RET belongs to its extent. -/
theorem wrong_extent_rejected :
    ELF.FunctionWindow.check file table selected.window shortExtent.bytes = true ∧
    shortExtent.check file name = false ∧
    shortExtent.admit file name caller.prior = .error .invalidImage := by
  have rejected : shortExtent.check file name = false := by decide +kernel
  exact ⟨by decide +kernel, rejected, rejected_admit _ _ rejected⟩

/-- This is an independently inhabited, current resource call with exactly
the same bytes, caller slot and installed file, at the other executable copy. -/
def copyEnvironment : CallResources.Domain.Initial := { environment with code := 0x500120 }

theorem copyPresent : CallResources.Domain.Facts copyEnvironment :=
  CallResources.Domain.check_sound (by decide +kernel)

def copyResource : Resources spec := Domain.resource copyEnvironment spec (9 : Word)
def copyMachine : State := Domain.initial copyEnvironment spec (9 : Word)

theorem copyPre : ResourcePre spec bytes copyResource copyMachine :=
  Domain.resource_pre copyPresent spec (9 : Word) rfl trivial

/-- Even genuine current authority and executable byte equality elsewhere
cannot supply the exact selected-address witness for this final ELF. -/
theorem same_bytes_wrong_address_rejected :
    ResourcePre spec bytes copyResource copyMachine ∧
    CodeAt copyMachine.memory copyMachine.rip bytes ∧
    ELF.FunctionWindow.TextUnchanged (AddressSpace.toMemory loaded.space)
      copyMachine.memory selected.window bytes.length ∧
    ¬ ∃ call : ELFLoadedCall spec file name certificate.input, call.initial = copyMachine := by
  refine ⟨copyPre, copyPre.machine.code, fun _ _ => ⟨rfl, rfl⟩, ?_⟩
  rintro ⟨call, same⟩
  have selectedAddress := call.entry
  rw [same] at selectedAddress
  exact (by decide +kernel : (0x500120 : Word) ≠ 0x400088) selectedAddress

/-- Change the last selected byte after admission; retain execute permission
and every other memory observation. The stale ELF admission is insufficient. -/
def changedText : Memory :=
  { AddressSpace.toMemory loaded.space with
    read := fun address => if address = 0x40008c then some 0x90
      else (AddressSpace.toMemory loaded.space).read address }

/-- Retain every byte but revoke execution at the selected RET. A comparison
of readable contents alone would incorrectly admit this current memory. -/
def noExecute : Memory :=
  { AddressSpace.toMemory loaded.space with
    executable := fun address => if address = 0x40008c then false
      else (AddressSpace.toMemory loaded.space).executable address }

private theorem bad_current_rejected (memory : Memory)
    (bad : fetchByte memory (selected.window.base + 4) ≠ .ok 0xc3) :
    ¬ ∃ call : ELFLoadedCall spec file name certificate.input, call.initial.memory = memory := by
  rintro ⟨call, same⟩
  have fetched := call.code.2 4 0xc3 (by rfl)
  rw [call.entry, same] at fetched
  exact bad fetched

theorem changed_text_rejected :
    ELF.checkCode changedText selected.window.base bytes = false ∧
    ¬ ∃ call : ELFLoadedCall spec file name certificate.input,
      call.initial.memory = changedText := by
  refine ⟨by decide +kernel, bad_current_rejected changedText ?_⟩
  intro wrong
  have observed : fetchByte changedText (selected.window.base + 4) = .ok 0x90 := rfl
  have same : (0x90 : Byte) = 0xc3 := Except.ok.inj (observed.symm.trans wrong)
  exact (by decide +kernel : (0x90 : Byte) ≠ 0xc3) same

theorem changed_execute_authority_rejected :
    ELF.checkCode noExecute selected.window.base bytes = false ∧
    ¬ ∃ call : ELFLoadedCall spec file name certificate.input,
      call.initial.memory = noExecute := by
  refine ⟨by decide +kernel, bad_current_rejected noExecute ?_⟩
  intro wrong
  have denied : fetchByte noExecute (selected.window.base + 4) =
      .error (.inaccessibleInstruction 0x40008c) := rfl
  rw [denied] at wrong
  cases wrong

def ended : Borrowing.State :=
  { (resource 9).shared with loans := fun query =>
    if query = (resource 9).call.stackLoan then none else (resource 9).shared.loans query }

def revoked : Resources spec := { resource 9 with shared := ended }

/-- A successful production loan-ending operation leaves RAM, permissions,
owners and epochs intact. Its result cannot be a current final-ELF call. -/
theorem lost_loan_rejected :
    Borrowing.finishLoan (resource 9).shared (Threads.principal (resource 9).call.worker)
      (resource 9).call.stackLoan = .ok ended ∧
    ended.resources = (resource 9).shared.resources ∧
    ¬ ∃ call : ELFLoadedCall spec file name certificate.input, call.resource = revoked := by
  obtain ⟨loan, live, borrower, _⟩ := (pre 9 (fun _ => 0) 0).current.contract.stackLoan
  simp only [BitVec.ofNat_eq_ofNat] at live borrower
  refine ⟨?_, rfl, ?_⟩
  · simp [Borrowing.finishLoan, Borrowing.authorize, live, borrower, ended]
  · rintro ⟨call, same⟩
    have held := call.pre.current.contract.stackLoan
    rw [same] at held
    obtain ⟨_, live, _, _⟩ := held
    simp [revoked, ended] at live

/-- Apply the generic theorem to ANY call of this certificate, independent of
the convenience constructor's useful value, registers or current OS world. -/
theorem every_loaded_call (call : ELFLoadedCall spec file name certificate.input) :
    AllExecutions call.initial (fun result =>
      Post spec (resourceInput call.resource) call.initial result.state ∧
      CallResources.Current call.resource.call call.resource.shared result.state) ∧
    Grading.ReadOnlyPolicy call.initial
      (CallResources.Current call.resource.call call.resource.shared)
      (fun _ => CallResources.ReadAllowed call.resource.call call.resource.shared) :=
  certificate.resource call

/-- Actual reachable prefixes keep original current resources; either AF
choice enables a real step and every observed read has current authority. -/
theorem prefix_authority (value : Word) (registers : Register → Word) (flags : Word)
    (before : State) (reachable : Reachable (machine value registers flags) before) :
    CallResources.Current (resource value).call (resource value).shared before ∧
    Grading.DecodesReadOnly before ∧
    ∀ af, ∃ observation, step af before = .ok observation ∧
      (∀ read ∈ observation.reads,
        CallResources.ReadAllowed (resource value).call (resource value).shared read ∧
        OperandReadSucceeds before read) ∧
      match observation.result with
      | .next after | .returned after => after.memory = before.memory
      | .atomic _ _ | .syscall _ => False :=
  (every_loaded_call (call value registers flags)).2 before reachable

-- Independently supplied wrapping, high-bit and full64 results for calls
-- beyond value 7. All unbound registers, flags and complete AF streams remain
-- universally quantified. Zero also checks the absence of a usefulness gate.
example (registers : Register → Word) (flags : Word) (choices : Choices) :=
  numeric_result 0xffffffffffffffff 0xfffffffffffffffe (by decide +kernel) registers flags choices
example (registers : Register → Word) (flags : Word) (choices : Choices) :=
  numeric_result 0x8000000000000000 0 (by decide +kernel) registers flags choices
example (registers : Register → Word) (flags : Word) (choices : Choices) :=
  numeric_result 0x80000000 0x100000000 (by decide +kernel) registers flags choices
example (registers : Register → Word) (flags : Word) (choices : Choices) :=
  numeric_result 0 0 (by decide +kernel) registers flags choices

#print axioms Examples.Verification.DoubleELF.certificate
#print axioms Examples.Verification.DoubleELF.useful_execution
#print axioms Examples.Verification.DoubleELF.numeric_result
#print axioms same_bytes_wrong_address_rejected
#print axioms changed_text_rejected
#print axioms changed_execute_authority_rejected
#print axioms lost_loan_rejected
#print axioms every_loaded_call
#print axioms prefix_authority

end EDSL.Tests.ELFCertificate

#audit_edsl
