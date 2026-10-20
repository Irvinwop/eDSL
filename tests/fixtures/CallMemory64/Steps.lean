/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallMemory64Programs
import EDSL.OS.CallMemory64.Coverage
import EDSL.CallStack.Geometry
import EDSL.CallStack.Certificates

set_option warningAsError true

namespace EDSL.CallMemory64.Compiler
open X86 OS

theorem node_fetch_bound (profile : Profile) (node : Node) :
    offset profile node + (instruction profile node).length ≤ (bytes profile).length := by
  cases profile <;> cases node <;> decide

theorem node_fetchWithin {profile : Profile} {frame : StackFrame.Descriptor} {state : State}
    (code : CodeAt state.memory frame.call.code (bytes profile))
    (same : frame.call.bytes = bytes profile) (node : Node)
    (pc : state.rip = frame.call.code + BitVec.ofNat 64 (offset profile node)) :
    CallStack.FetchWithin frame state := by
  apply CallStack.Certificates.fetchWithin_of_code (by simpa only [same] using code)
    (by rw [same]; cases profile <;> decide)
    (by rw [same]; exact inside profile node) pc
  · simpa only [same] using static_decode profile node
  · rw [same]
    exact node_fetch_bound profile node

theorem current_code {descriptor : OS.CallMemory64.Descriptor} {shared : Borrowing.State}
    {state : State} {profile : Profile} (current : OS.CallMemory64.Current descriptor shared state)
    (same : descriptor.frame.call.bytes = bytes profile) :
    CodeAt state.memory descriptor.frame.call.code (bytes profile) := by
  rw [current.coupled, ← same]
  exact current.contract.stack.pureCall.code

theorem decode_sequential {profile : Profile} {state : State} {base : Word}
    {node : Node} {operation : Sequential.Instruction}
    (code : CodeAt state.memory base (bytes profile))
    (pc : state.rip = base + BitVec.ofNat 64 (offset profile node))
    (static : Sequential.decodeAt (Sequential.codeState (bytes profile) (offset profile node)) =
      .ok operation) : Sequential.decodeAt state = .ok operation :=
  Sequential.decodeAt_transport
    (Sequential.code_fetch_transport code (by cases profile <;> decide)
      (offset profile node) (inside profile node) state rfl pc) static

theorem call_target {base : Word} {state : State}
    (pc : state.rip = base + 1) : CallReturn.callTarget state 5 = base + 11 := by
  simp [CallReturn.callTarget, CallReturn.returnAddress, pc, BitVec.add_assoc]

theorem call_continuation {base : Word} {state : State}
    (pc : state.rip = base + 1) : CallReturn.returnAddress state = base + 6 := by
  simp [CallReturn.returnAddress, pc, BitVec.add_assoc]

theorem call_addresses {profile : Profile} {base : Word} {state : State}
    (code : CodeAt state.memory base (bytes profile)) (pc : state.rip = base + 1) :
    canonical (CallReturn.callTarget state 5) = true ∧
      canonical (CallReturn.returnAddress state) = true := by
  rw [call_target pc, call_continuation pc]
  exact ⟨Sequential.code_canonical_offset code 11 (by cases profile <;> decide),
    Sequential.code_canonical_offset code 6 (by cases profile <;> decide)⟩

/-- A DATA store retains each currently owned private word, using full coupled
RAM, actual mutation effects and allocation separation. -/
theorem data_preserves_private {descriptor : OS.CallMemory64.Descriptor}
    {before after : Borrowing.State} {initial final : State} {value location : Word}
    (first : OS.CallMemory64.Current descriptor before initial)
    (last : OS.CallMemory64.Current descriptor after final)
    (effect : Borrowing.StoreEffect64 before after descriptor.target value)
    (slot : StackFrame.Slot descriptor.frame location) :
    readWord final.memory location = readWord initial.memory location := by
  rw [first.coupled, last.coupled]
  apply readWord_congr
  apply AddressSpace.agrees_read
  intro index bound
  have privateByte : descriptor.frame.region.Contains (location + BitVec.ofNat 64 index) := by
    have valid := of_decide_eq_true first.contract.stack.region_valid
    have operand : (AddressSpace.qwordRegion location).valid = true := by
      apply decide_eq_true
      change 0 < 8 ∧ location.toNat + 8 ≤ 2^64 ∧
        (location.toNat + 8 ≤ 2^47 ∨ 2^64 - 2^47 ≤ location.toNat)
      have fits : descriptor.frame.region.base.toNat ≤ location.toNat ∧
          location.toNat + 8 ≤ descriptor.frame.region.base.toNat + descriptor.frame.region.length := slot
      omega
    exact Borrowing.subregion_inside slot (Ownership.addresses_inside _ operand _
      (List.mem_map.mpr ⟨index, List.mem_range.mpr bound, rfl⟩))
  exact effect.outside _ (fun data => first.contract.target_outside_private data privateByte)

end EDSL.CallMemory64.Compiler
