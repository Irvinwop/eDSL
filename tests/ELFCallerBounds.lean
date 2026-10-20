/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.ELF.CallerResources.Stack
import EDSL.Corpus.BufferResources
import EDSL.Corpus.BufferCertificate
import tests.ELFFunctionBounds
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.ELFCallerBounds
open X86 X86.Sequential OS OS.AddressSpace ELF
open CallResources ELF.CallerResources

-- Extend only the LOAD's memory size. The same literal 68-byte named function
-- is followed by twelve RX BSS bytes outside its selected extent.
def file : List Byte := ELFFunctionSymbol.putLE ELFFunctionBounds.file 104 8 80
def input : ELF.FunctionInput :=
  { ELFFunctionBounds.input with table :=
    { ELFFunctionBounds.input.table with programs :=
      [⟨1, 0x400080, ⟨0x80, 0x400080, 68, 80, 5, 4096⟩⟩] } }
abbrev name := ELFFunctionBounds.name

theorem checked : input.checkWith 68 file name = true := by decide +kernel
example : input.check file name = false := by decide +kernel
example : input.checkWith 67 file name = false := by decide +kernel
-- The caller/certificate path must still authenticate the complete suffix.
example : input.checkWith 68 (file.set (0x80 + 66) 0xc3) name = false := by decide +kernel
example : ({ input with bytes := input.bytes.take 64 } : ELF.FunctionInput).checkWith
    68 file name = false := by decide +kernel

abbrev caller := Stack.standard

theorem fresh : ELF.fresh input.table.image caller.prior = true :=
  Stack.check_sound input.table.image caller.stack caller.returnAddress (by decide +kernel)

def environment : Domain.Initial := ELF.CallerResources.initial file input caller

theorem facts : Domain.Facts environment :=
  Corpus.ELFResources.initial_factsWith checked fresh Stack.standard_facts (by decide +kernel)

-- The ordinary domain constructor issues real compatible code and caller loans.
-- The input aliases the entire read-only code buffer using that same code loan.
def resource : BufferCall.Resources Grading.ByteScan.spec :=
  ⟨Domain.shared environment, Domain.call environment,
    ⟨environment.code, environment.bytes⟩, fun _ => 0⟩

theorem resourceContract : BufferCall.ResourceContract resource resource.shared := by
  refine ⟨Domain.contract facts, ?_, ?_⟩
  · intro buffer member
    have same : buffer = ⟨environment.code, environment.bytes⟩ := by
      simpa only [Grading.ByteScan.spec, resource, List.mem_singleton] using member
    subst buffer
    exact facts.code.readable
  · intro buffer member _
    have same : buffer = ⟨environment.code, environment.bytes⟩ := by
      simpa only [Grading.ByteScan.spec, resource, List.mem_singleton] using member
    subst buffer
    exact Domain.code_held environment

def machine : State := Domain.machine environment
  (fun register => if register = .rdi then environment.code else
    if register = .rsi then BitVec.ofNat 64 environment.bytes.length else 0) 0x202

theorem resourcePre : BufferCall.ResourcePre Grading.ByteScan.spec input.bytes resource machine := by
  refine ⟨⟨resourceContract, rfl⟩, rfl, rfl, ?_, ?_, ?_⟩
  · simp only [machine, Domain.machine, resource, Domain.call, ↓reduceIte]
  · change (68 : Nat) < 2^64
    decide
  · intro index argument binding
    obtain ⟨index, bound⟩ := index
    match index with
    | 0 =>
      simp [resource, Grading.ByteScan.spec] at binding
      subst argument
      rfl
    | 1 =>
      simp [resource, Grading.ByteScan.spec] at binding
      subst argument
      rfl
    | index + 2 => simp [resource, Grading.ByteScan.spec] at binding

-- This is an actual useful LoadedCall at the supplied address, with current
-- resources and EVERY installed cell/permission retained. It is no body claim.
def call : Corpus.Buffer.LoadedCall .firstBoundedNulLength file name input 68 where
  prior := caller.prior
  loaded := ELF.CallerResources.loaded file input caller
  admitted := Corpus.ELFResources.admittedWith checked fresh
  resource := resource
  initial := machine
  useful := by change ELFFunctionBounds.bytes ≠ []; decide +kernel
  pre := resourcePre
  entry := rfl
  text := by intro offset bound; exact ⟨rfl, rfl⟩
  retainedImage := by intro address original found; exact found

theorem code : CodeAt machine.memory 0x400080 ELFFunctionBounds.bytes := call.code

-- The indexed BUFFER space agrees with the COMPLETE installed space, including
-- the unselected RX BSS tail. Its permissions cannot be reconstructed loosely.
theorem executablePermissions : ∀ segment ∈ input.table.image.segments,
    segment.permissions.executable = true → segment.permissions = readExecute := by
  intro segment member _
  change segment ∈ [⟨0x80, 0x400080, 68, 80, 5, 4096⟩] at member
  have same := List.mem_singleton.mp member
  subst segment
  rfl

theorem indexedSpace : Corpus.BufferResources.programSpace file input =
    (Corpus.BufferResources.installed file input).space :=
  Corpus.BufferResources.programSpace_eqWith checked executablePermissions

theorem finalCodeCell : (Corpus.BufferResources.installed file input).space.cells 0x4000c3 =
    some ⟨0xc3, readExecute⟩ :=
  Corpus.BufferResources.installed_cellWith checked executablePermissions 67 (by decide +kernel)

theorem unselectedBssRetained :
    (Corpus.BufferResources.programSpace file input).cells 0x4000c4 = some ⟨0, readExecute⟩ ∧
    call.resource.shared.resources.space.cells 0x4000c4 = some ⟨0, readExecute⟩ := by
  constructor
  · rw [indexedSpace]
    buffer_resource_kernel_rfl
  · buffer_resource_kernel_rfl

def hiddenSuffix : Space := protectUnchecked environment.space ⟨0x4000c3, 1⟩ readOnly

-- Real address-space protection keeps the final byte readable but removes
-- execute authority. Current-code transport must reject this changed suffix.
theorem suffixExecuteRequired :
    AddressSpace.protect environment.space ⟨0x4000c3, 1⟩ readOnly = .ok hiddenSuffix ∧
    readDataByte (toMemory hiddenSuffix) 0x4000c3 = .ok 0xc3 ∧
    ¬FunctionWindow.TextUnchanged machine.memory (toMemory hiddenSuffix)
      input.function.window input.bytes.length := by
  refine ⟨rfl, rfl, ?_⟩
  intro unchanged
  have executable := (unchanged 67 (by decide +kernel)).2
  change false = true at executable
  cases executable

-- A read in the selected suffix has current manager authority, beyond the old
-- default cap. The adjacent readable BSS byte grants no extra input authority.
theorem finalByteAllowed : BufferCall.ReadAllowed resource ⟨.data, 0x4000c3, 1⟩ := by
  have footprint : BufferCall.DataRead (Grading.ByteScan.spec.buffers resource.value)
      ⟨.data, 0x4000c3, 1⟩ := by
    refine ⟨rfl, ⟨environment.code, environment.bytes⟩, by simp [Grading.ByteScan.spec, resource], ?_⟩
    unfold BufferCall.Buffer.Contains
    decide +kernel
  exact .inr ⟨footprint, resourceContract.dataRead_permission footprint⟩

theorem readableNeighborDenied :
    readDataByte machine.memory 0x4000c4 = .ok 0 ∧
    ¬BufferCall.ReadAllowed resource ⟨.data, 0x4000c4, 1⟩ := by
  refine ⟨rfl, ?_⟩
  intro allowed
  rcases allowed with stack | data
  · cases stack.1
  · obtain ⟨_, buffer, member, span⟩ := data.1
    have same : buffer = ⟨environment.code, environment.bytes⟩ := by
      simpa only [Grading.ByteScan.spec, resource, List.mem_singleton] using member
    subst buffer
    have outside : ¬(BufferCall.Buffer.mk environment.code environment.bytes).Contains 0x4000c4 1 := by
      unfold BufferCall.Buffer.Contains
      decide +kernel
    exact outside span

theorem replacementStackDenied :
    ¬BufferCall.ReadAllowed resource ⟨.stack, 0x400080, 8⟩ := by
  intro allowed
  rcases allowed with stack | data
  · exact (by decide +kernel : (0x400080 : Word) ≠ resource.call.stack) stack.2.1
  · cases data.1.1

def ended : Borrowing.State :=
  { resource.shared with loans := fun query => if query = 0 then none else resource.shared.loans query }

-- Finish the real loan while leaving readable executable RAM unchanged.
-- A snapshot cannot substitute for the revoked current code/input authority.
theorem revokedCodeDenied :
    Borrowing.finishLoan resource.shared (Threads.principal caller.worker) 0 = .ok ended ∧
    toMemory ended.resources.space = machine.memory ∧
    ¬BufferCall.ResourceContract resource ended := by
  refine ⟨rfl, rfl, ?_⟩
  intro claimed
  obtain ⟨loan, live, _, _⟩ := claimed.call.codeLoan
  change none = some loan at live
  cases live

-- A preexisting slot outside the function but inside its rounded LOAD page
-- still blocks admission. Raising maxBytes never weakens page freshness.
def collision : Space := Stack.prior 0x400800 0x654321

theorem collisionNotFresh : ELF.fresh input.table.image collision = false := by
  cases observed : ELF.fresh input.table.image collision with
  | false => rfl
  | true =>
    have unmapped : allUnmapped collision
        (⟨0x80, 0x400080, 68, 80, 5, 4096⟩ : ELF.Segment).pageRegion = true :=
      List.all_eq_true.mp observed _ List.mem_cons_self
    have absent := allUnmapped_inside _ _ unmapped 0x400800 (by decide +kernel)
    change some (⟨0x21, readOnly⟩ : Cell) = none at absent
    cases absent

theorem collisionRejected : input.admitWith 68 file name collision = .error .mappingCollision := by
  have named : FunctionSymbol.checkWith 68 file input.table input.metadata name
      input.function input.bytes = true := checked
  have window : FunctionWindow.checkWith 68 file input.table input.function.window input.bytes = true :=
    (Bool.and_eq_true_iff.mp named).2
  simp only [FunctionInput.admitWith, FunctionSymbol.admitWith, named, ↓reduceIte,
    FunctionWindow.admitWith, window, collisionNotFresh, Bool.false_eq_true, ↓reduceIte]

-- Static admission establishes no registered scan semantics for this constant-42
-- fixture. Only an explicit independent SemanticClaim may supply a certificate.
def conditionalCertificate
    (semantics : Grading.BufferTask.SemanticClaim .firstBoundedNulLength input.bytes) :
    Corpus.Buffer.Certificate .firstBoundedNulLength file name 68 :=
  Corpus.Buffer.Certificate.ofLoadedCallWith 68 input checked semantics call

theorem conditionalBinding
    (semantics : Grading.BufferTask.SemanticClaim .firstBoundedNulLength input.bytes) :
    FunctionWindow.Selection file input.table.image input.function.window input.bytes 68 :=
  (conditionalCertificate semantics).binding.2.2.2

theorem conditionalPolicy
    (semantics : Grading.BufferTask.SemanticClaim .firstBoundedNulLength input.bytes) :
    AllExecutions call.initial (fun result =>
      BufferCall.Post Grading.ByteScan.spec (BufferCall.resourceInput call.resource)
        call.initial result.state ∧ BufferCall.Current call.resource result.state) ∧
    Grading.ReadOnlyPolicy call.initial (BufferCall.Current call.resource)
      (fun _ read => BufferCall.ReadAllowed call.resource read) :=
  (conditionalCertificate semantics).resource call

end EDSL.Tests.ELFCallerBounds

#print axioms EDSL.ELF.CallerResources.initial_factsWith
#print axioms EDSL.Corpus.BufferResources.programSpace_eqWith
#print axioms EDSL.Corpus.Buffer.Certificate.ofLoadedCallWith
#print axioms EDSL.Corpus.Buffer.Certificate.resource
#print axioms EDSL.Corpus.Buffer.Certificate.useful_execution
#print axioms EDSL.Tests.ELFCallerBounds.facts
#print axioms EDSL.Tests.ELFCallerBounds.resourcePre
#print axioms EDSL.Tests.ELFCallerBounds.call
#print axioms EDSL.Tests.ELFCallerBounds.conditionalPolicy
#audit_edsl
