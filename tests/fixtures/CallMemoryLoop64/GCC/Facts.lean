/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallMemoryLoop64.GCC.Steps

set_option warningAsError true

namespace EDSL.CallMemoryLoop64.GCC
open X86 OS

/-- RBP/RBX are temporarily used after their actual incoming words are saved.
The other callee-saved registers and every nonarithmetic flag remain framed. -/
def workingRegisters : List Register := CallStack.clobbers ++ [.rbp, .rbx]

structure Frame (initial final : State) : Prop where
  preserved : ∀ register, register ∉ workingRegisters → final.registers register = initial.registers register
  flags : final.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask

theorem Frame.refl (state : State) : Frame state state := ⟨fun _ _ => rfl, rfl⟩
theorem Frame.trans {first middle final : State} (left : Frame first middle) (right : Frame middle final) :
    Frame first final := ⟨fun r outside => (right.preserved r outside).trans (left.preserved r outside),
      right.flags.trans left.flags⟩

theorem Frame.full {initial final : State} (frame : Frame initial final)
    (rbp : final.registers .rbp = initial.registers .rbp)
    (rbx : final.registers .rbx = initial.registers .rbx) :
    ∀ register, register ∉ CallStack.clobbers → final.registers register = initial.registers register := by
  intro register outside
  by_cases bp : register = .rbp
  · subst register; exact rbp
  by_cases bx : register = .rbx
  · subst register; exact rbx
  exact frame.preserved register (by simp [workingRegisters, outside, bp, bx])

theorem frame_write (state : State) (destination : Register) (value pc flags : Word) (memory : Memory)
    (allowed : destination ∈ workingRegisters)
    (flagsFrame : flags &&& ~~~arithmeticFlagMask = state.flags &&& ~~~arithmeticFlagMask) :
    Frame state { state.writeRegister destination value with rip := pc, flags := flags, memory := memory } := by
  refine ⟨?_, flagsFrame⟩
  intro register outside
  have different : register ≠ destination := by intro same; subst register; exact outside allowed
  simp [State.writeRegister, different]

theorem frame_move (state : State) (destination source : Register) (allowed : destination ∈ workingRegisters) :
    Frame state (moved state destination source) := frame_write state destination _ _ _ _ allowed rfl

theorem frame_push (state : State) (source : Register) : Frame state (pushed state source) :=
  frame_write state .rsp _ _ _ _ (by decide) rfl

theorem frame_call (state : State) : Frame state (called state) :=
  frame_write state .rsp _ _ _ _ (by decide) rfl

theorem frame_test (state : State) (af : Bool) : Frame state (tested state af) :=
  ⟨fun _ _ => rfl, Sequential.logicalFlags64_preserves ..⟩

theorem frame_decrement (state : State) : Frame state (decremented state) :=
  frame_write state .rbx _ _ _ _ (by decide) (Sequential.decFlags64_preserves ..)

theorem frame_pc (state : State) (pc : Word) : Frame state (atPC state pc) := ⟨fun _ _ => rfl, rfl⟩

theorem frame_store (state : State) (world : Shared) : Frame state (stored state world) := ⟨fun _ _ => rfl, rfl⟩

theorem frame_load (state : State) (value : Word) : Frame state (loaded state value) :=
  frame_write state .rax _ _ _ _ (by decide) rfl

theorem frame_advance (state : State) : Frame state (advanced state) :=
  frame_write state .rsi _ _ _ _ (by decide) rfl

theorem frame_pop (state : State) (destination : Register) (value : Word) (allowed : destination ∈ workingRegisters) :
    Frame state (popped state destination value) := by
  refine (frame_write state .rsp (state.registers .rsp + 8) state.rip state.flags state.memory
    (by decide) rfl).trans ?_
  exact frame_write _ destination _ _ _ _ allowed rfl

theorem frame_finish (state : State) (target : Word) : Frame state (finished state target) :=
  frame_write state .rsp _ _ _ _ (by decide) rfl

theorem depth_slot {descriptor shared state} (current : Current descriptor shared state)
    (capacity : 32 ≤ descriptor.frame.capacity) {depth : Nat} (lower : 8 ≤ depth) (upper : depth ≤ 32) :
    StackFrame.Slot descriptor.frame (descriptor.frame.top - BitVec.ofNat 64 depth) :=
  CallStack.private_slot_at_depth current.contract.stack lower (Nat.le_trans upper capacity)

theorem depth_nat {descriptor shared state} (current : Current descriptor shared state)
    (capacity : 32 ≤ descriptor.frame.capacity) {depth : Nat} (bound : depth ≤ 32) :
    (descriptor.frame.top - BitVec.ofNat 64 depth).toNat = descriptor.frame.top.toNat - depth := by
  have below : depth ≤ descriptor.frame.top.toNat :=
    Nat.le_trans bound (Nat.le_trans capacity current.contract.stack.topBound)
  have small : depth < 2^64 := Nat.lt_of_le_of_lt below descriptor.frame.top.isLt
  have natural : (BitVec.ofNat 64 depth).toNat = depth := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  rw [BitVec.toNat_sub_of_le (by change (BitVec.ofNat 64 depth).toNat ≤ descriptor.frame.top.toNat; omega), natural]

theorem depth_disjoint {descriptor shared state} (current : Current descriptor shared state)
    (capacity : 32 ≤ descriptor.frame.capacity) {first last : Nat}
    (firstBound : first ≤ 32) (lastBound : last ≤ 32)
    (separate : first + 8 ≤ last ∨ last + 8 ≤ first) :
    Ownership.Disjoint (AddressSpace.qwordRegion (descriptor.frame.top - BitVec.ofNat 64 first))
      (AddressSpace.qwordRegion (descriptor.frame.top - BitVec.ofNat 64 last)) := by
  have a := depth_nat current capacity firstBound
  have b := depth_nat current capacity lastBound
  have top := current.contract.stack.topBound
  change (descriptor.frame.top - BitVec.ofNat 64 first).toNat + 8 ≤
      (descriptor.frame.top - BitVec.ofNat 64 last).toNat ∨
    (descriptor.frame.top - BitVec.ofNat 64 last).toNat + 8 ≤
      (descriptor.frame.top - BitVec.ofNat 64 first).toNat
  rw [a, b]
  omega

/-- The two actual saved incoming callee words. Their locations refer to the
frozen original S, even during a private return at S-32. -/
structure Saved (descriptor : Descriptor) (initial state : State) : Prop where
  rbp : readWord state.memory (descriptor.frame.top - 8) = .ok (initial.registers .rbp)
  rbx : readWord state.memory (descriptor.frame.top - 16) = .ok (initial.registers .rbx)

theorem Saved.sameMemory {descriptor initial before after} (saved : Saved descriptor initial before)
    (memory : after.memory = before.memory) : Saved descriptor initial after := by
  exact ⟨by simpa only [memory] using saved.rbp, by simpa only [memory] using saved.rbx⟩

theorem Saved.private_store {descriptor before after initial first last address value}
    (current : Current descriptor before first) (next : Current descriptor after last)
    (capacity : 32 ≤ descriptor.frame.capacity) (saved : Saved descriptor initial first)
    (effect : Borrowing.StoreEffect64 before after address value)
    (addressEq : address = descriptor.frame.top - 32) : Saved descriptor initial last := by
  subst address
  refine ⟨?_, ?_⟩
  · exact (OS.CallMemory64.store64_preserves_private current next effect
      (depth_slot current capacity (by decide : 8 ≤ 8) (by decide))
      (depth_disjoint current capacity (by decide : 32 ≤ 32) (by decide : 8 ≤ 32) (by decide))).trans saved.rbp
  · exact (OS.CallMemory64.store64_preserves_private current next effect
      (depth_slot current capacity (by decide : 8 ≤ 16) (by decide))
      (depth_disjoint current capacity (by decide : 32 ≤ 32) (by decide : 16 ≤ 32) (by decide))).trans saved.rbx

theorem Saved.data_store {descriptor before after initial first last value}
    (current : Current descriptor before first) (next : Current descriptor after last)
    (capacity : 32 ≤ descriptor.frame.capacity) (saved : Saved descriptor initial first)
    (effect : Borrowing.StoreEffect64 before after descriptor.target value) : Saved descriptor initial last :=
  ⟨(OS.CallMemory64.data_preserves_private current next effect
      (depth_slot current capacity (by decide : 8 ≤ 8) (by decide))).trans saved.rbp,
    (OS.CallMemory64.data_preserves_private current next effect
      (depth_slot current capacity (by decide : 8 ≤ 16) (by decide))).trans saved.rbx⟩

/-- Private pushes/CALLs retain the current DATA word, through actual owner
readback rather than an assumed immutable CPU memory. -/
theorem private_target {descriptor before after first last address value}
    (current : Current descriptor before first) (next : Current descriptor after last)
    (slot : StackFrame.Slot descriptor.frame address)
    (success : Borrowing.mutate before (.store64 descriptor.owner descriptor.frame.ticket address value) =
      .ok (after, none)) : readWord last.memory descriptor.target = readWord first.memory descriptor.target := by
  obtain ⟨old, owned, observed, _⟩ := current.contract.data_read
  have retained := OS.CallMemory64.private_store64_preserves_data current.contract slot success owned
  rw [current.coupled, next.coupled, observed]
  exact Borrowing.loadOwnedWord64_readWord _ _ _ _ _ retained

/-- Constant private-stack footprint and a full64 remaining-count invariant.
The sum is modular; the decreasing rank itself is an ordinary natural. -/
structure Invariant (resource : Resources) (initial state : State) (remaining : Nat) : Prop where
  pc : state.rip = resource.descriptor.frame.call.code + 9
  stack : state.registers .rsp = resource.descriptor.frame.top - 24
  pointer : state.registers .rbp = resource.descriptor.target
  counter : (state.registers .rbx).toNat = remaining
  total : state.registers .rsi + BitVec.ofNat 64 remaining = resource.value + resource.count
  remaining_le : remaining ≤ resource.count.toNat
  stored : readWord state.memory resource.descriptor.target =
    if remaining = resource.count.toNat then readWord initial.memory resource.descriptor.target
    else .ok (state.registers .rsi - 1)
  saved : Saved resource.descriptor initial state
  frame : Frame initial state

end EDSL.CallMemoryLoop64.GCC
