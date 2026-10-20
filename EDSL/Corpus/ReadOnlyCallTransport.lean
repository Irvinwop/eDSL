/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.ReadOnlyCalls

set_option autoImplicit false
set_option warningAsError true

/-! Reuse a current buffer call after attaching another code extent in the
same complete memory. Original caller and input authority retain their exact
identifiers. Result-only views preserve admission independently of execution. -/

namespace EDSL.Corpus.ReadOnlyCallTransport
open X86 OS OS.AddressSpace BufferCall
open BufferResources (Managed)

/-- Only the shared state and code fields change. The attachment requests no
new inputs; even unused empty-buffer identifiers remain exactly as supplied. -/
def retarget {spec : Spec} (resource : Resources spec) (bytes : List Byte) {before : Managed}
    {entry : Word}
    (attached : ReadOnlyCalls.Attached before resource.call.worker ⟨entry, bytes.length⟩ []) :
    Resources spec :=
  { resource with
    shared := attached.managed.shared
    call := { resource.call with
      code := entry, bytes := bytes, codeLoan := attached.codeLoan } }

/-- Equality covers every mapped cell and all three permission bits. -/
theorem retarget_space {spec : Spec} (resource : Resources spec) (bytes : List Byte)
    {before : Managed} {entry : Word}
    (attached : ReadOnlyCalls.Attached before resource.call.worker ⟨entry, bytes.length⟩ [])
    (same : before.shared = resource.shared) :
    (retarget resource bytes attached).shared.resources.space = resource.shared.resources.space :=
  attached.space.trans (congrArg (fun shared : Borrowing.State => shared.resources.space) same)

/-- New executable bytes must be proved in the original complete memory.
Their live code loan comes from the attachment; all other authority comes
from the original current contract and the checked manager extension. -/
theorem retarget_contract {spec : Spec} {resource : Resources spec} {before : Managed}
    {entry : Word} {bytes : List Byte}
    (attached : ReadOnlyCalls.Attached before resource.call.worker ⟨entry, bytes.length⟩ [])
    (same : before.shared = resource.shared)
    (original : ResourceContract resource resource.shared)
    (code : CodeAt (toMemory resource.shared.resources.space) entry bytes) :
    ResourceContract (retarget resource bytes attached) (retarget resource bytes attached).shared := by
  refine ⟨⟨attached.managed.valid, attached.codeHeld, ?_, ?_, ?_,
    original.call.returnCanonical, original.call.stackBound,
    original.call.postStackCanonical⟩, ?_, ?_⟩
  · apply attached.original_loan
    rw [same]
    exact original.call.stackLoan
  · change CodeAt (toMemory (retarget resource bytes attached).shared.resources.space) entry bytes
    rw [retarget_space resource bytes attached same]
    exact code
  · change readWord (toMemory (retarget resource bytes attached).shared.resources.space)
      resource.call.stack = .ok resource.call.returnAddress
    rw [retarget_space resource bytes attached same]
    exact original.call.stack
  · intro buffer member
    change BufferAt (toMemory (retarget resource bytes attached).shared.resources.space)
      buffer.base buffer.bytes
    rw [retarget_space resource bytes attached same]
    exact original.buffers buffer member
  · intro buffer member nonempty
    apply attached.original_loan
    rw [same]
    exact original.inputs buffer member nonempty

/-- Keep the original registers, flags and complete RAM, changing only RIP.
The mathematical domain and every argument binding are transported unchanged. -/
theorem retarget_pre {spec : Spec} {resource : Resources spec} {before : Managed}
    {entry : Word} {bytes oldBytes : List Byte} {initial : X86.State}
    (attached : ReadOnlyCalls.Attached before resource.call.worker ⟨entry, bytes.length⟩ [])
    (same : before.shared = resource.shared)
    (original : ResourcePre spec oldBytes resource initial)
    (code : CodeAt (toMemory resource.shared.resources.space) entry bytes) :
    ResourcePre spec bytes (retarget resource bytes attached) { initial with rip := entry } := by
  refine ⟨⟨retarget_contract attached same original.current.contract code, ?_⟩,
    rfl, rfl, original.stack, original.domain, original.arguments⟩
  change initial.memory = toMemory (retarget resource bytes attached).shared.resources.space
  rw [retarget_space resource bytes attached same]
  exact original.current.coupled

/-- Change only the mathematical return relation. Input type, domain,
usefulness, argument bindings, snapshots and exact resource handles are kept. -/
def resultView {spec : Spec} (resource : Resources spec)
    (result : spec.Input → Word → Prop) : Resources { spec with result := result } :=
  ⟨resource.shared, resource.call, resource.value, resource.inputLoan⟩

theorem resultView_contract_iff {spec : Spec} (resource : Resources spec)
    (result : spec.Input → Word → Prop) (shared : Borrowing.State) :
    ResourceContract (resultView resource result) shared ↔ ResourceContract resource shared := by
  constructor <;> intro contract <;> exact ⟨contract.call, contract.buffers, contract.inputs⟩

/-- This equates admission, not postconditions or semantic certificates. -/
theorem resultView_pre_iff {spec : Spec} (resource : Resources spec)
    (result : spec.Input → Word → Prop) (bytes : List Byte) (initial : X86.State) :
    ResourcePre { spec with result := result } bytes (resultView resource result) initial ↔
      ResourcePre spec bytes resource initial := by
  constructor <;> intro pre
  · exact ⟨⟨(resultView_contract_iff resource result resource.shared).mp pre.current.contract,
      pre.current.coupled⟩, pre.code, pre.entry, pre.stack, pre.domain, pre.arguments⟩
  · exact ⟨⟨(resultView_contract_iff resource result resource.shared).mpr pre.current.contract,
      pre.current.coupled⟩, pre.code, pre.entry, pre.stack, pre.domain, pre.arguments⟩

#print axioms retarget
#print axioms retarget_space
#print axioms retarget_contract
#print axioms retarget_pre
#print axioms resultView
#print axioms resultView_contract_iff
#print axioms resultView_pre_iff
end EDSL.Corpus.ReadOnlyCallTransport
#audit_edsl
