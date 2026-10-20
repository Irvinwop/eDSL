/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Memory64
import EDSL.X86.Sequential.Model

namespace EDSL.X86

/-- Bounded abstract locked-qword profile. Virtual checks do not establish
physical atomicity: interpretation requires coherent WB RAM, stable translation
and permissions, contiguous injective backing with compatible physical line/page
layout, and no unmanaged aliases, mixed-width, MMIO, DMA or non-temporal
interference. Physical LOCK refinement is a separate, unproved obligation. -/
def atomicAddressable64 (address : Word) : Bool :=
  qwordAddressable address && decide (address.toNat % 8 = 0 ∧
    address.toNat % 64 + 8 ≤ 64 ∧ address.toNat % 4096 + 8 ≤ 4096)

/-- Fixed-code support gate, independent of the full read/write preflight. -/
def dataOnly64 (memory : Memory) (address : Word) : Bool :=
  !memory.executable address && !memory.executable (address + 1) &&
    !memory.executable (address + 2) && !memory.executable (address + 3) &&
    !memory.executable (address + 4) && !memory.executable (address + 5) &&
    !memory.executable (address + 6) && !memory.executable (address + 7)

/-- Distinct full-width event; no interpretation as one or two DWORD events. -/
structure AtomicEvent64 where
  address : Word
  before : Word
  after : Word
  deriving DecidableEq, Repr

structure LogicalEvent64 where
  op : Sequential.LogicalOp
  mask : Word
  event : AtomicEvent64
  deriving DecidableEq, Repr

/-- One abstract indivisible transition. The byte-update helper by itself
claims no atomicity, and no load/store intermediate state is exposed here. -/
def RMWTransition64 (memory : Memory) (event : AtomicEvent64) (result : Memory) : Prop :=
  atomicAddressable64 event.address = true ∧ canStoreQWord memory event.address = true ∧
  loadQWord memory event.address = .ok event.before ∧
  result = writeQWordUnchecked memory event.address event.after

/-- Preflight every operand byte, read the current full word, compute, and
return exactly one labeled event with one functional eight-byte update. Even
an unchanged result requires write permission. `dataOnly64` is an additional
fixed-code execution gate, not an ordinary RAM permission. -/
def logicalRmwQWord (op : Sequential.LogicalOp) (memory : Memory)
    (address mask : Word) : Except Error (Memory × LogicalEvent64) := do
  if !atomicAddressable64 address then throw (.unsupportedAtomicAddress address)
  if !canStoreQWord memory address then throw (.writeDenied address)
  let old ← loadQWord memory address
  let value := op.eval old mask
  return (writeQWordUnchecked memory address value, ⟨op, mask, ⟨address, old, value⟩⟩)

theorem logicalRmwQWord_sound (op : Sequential.LogicalOp) (memory : Memory)
    (address mask : Word) (result : Memory × LogicalEvent64)
    (success : logicalRmwQWord op memory address mask = .ok result) :
    RMWTransition64 memory result.2.event result.1 ∧ result.2.op = op ∧
    result.2.mask = mask ∧ result.2.event.address = address ∧
    result.2.event.after = op.eval result.2.event.before mask := by
  by_cases supported : atomicAddressable64 address = true
  · by_cases allowed : canStoreQWord memory address = true
    · cases read : loadQWord memory address with
      | error fault => simp [logicalRmwQWord, supported, allowed, read] at success
      | ok old =>
        simp [logicalRmwQWord, supported, allowed, read] at success
        subst result
        exact ⟨⟨supported, allowed, read, rfl⟩, rfl, rfl, rfl, rfl⟩
    · simp [logicalRmwQWord, supported, allowed] at success
  · simp [logicalRmwQWord, supported] at success

theorem logicalRmwQWord_success (op : Sequential.LogicalOp) (memory : Memory)
    (address mask old : Word) (supported : atomicAddressable64 address = true)
    (allowed : canStoreQWord memory address = true) (read : loadQWord memory address = .ok old) :
    logicalRmwQWord op memory address mask = .ok
      (writeQWordUnchecked memory address (op.eval old mask),
        ⟨op, mask, ⟨address, old, op.eval old mask⟩⟩) := by
  simp [logicalRmwQWord, supported, allowed, read]

theorem logicalRmwQWord_enabled (op : Sequential.LogicalOp) (memory : Memory)
    (address mask : Word) (supported : atomicAddressable64 address = true)
    (allowed : canStoreQWord memory address = true) :
    ∃ result, logicalRmwQWord op memory address mask = .ok result := by
  obtain ⟨old, read⟩ := loadQWord_of_canStoreQWord memory address allowed
  exact ⟨_, logicalRmwQWord_success op memory address mask old supported allowed read⟩

theorem logicalRmwQWord_unsupported (op : Sequential.LogicalOp) (memory : Memory)
    (address mask : Word) (unsupported : atomicAddressable64 address = false) :
    logicalRmwQWord op memory address mask = .error (.unsupportedAtomicAddress address) := by
  simp [logicalRmwQWord, unsupported]

theorem logicalRmwQWord_denied (op : Sequential.LogicalOp) (memory : Memory)
    (address mask : Word) (supported : atomicAddressable64 address = true)
    (denied : canStoreQWord memory address = false) :
    logicalRmwQWord op memory address mask = .error (.writeDenied address) := by
  simp [logicalRmwQWord, supported, denied]

theorem RMWTransition64.readback {memory result : Memory} {event : AtomicEvent64}
    (transition : RMWTransition64 memory event result) :
    loadQWord result event.address = .ok event.after := by
  rw [transition.2.2.2]
  exact qword_load_after_write _ _ _ (Bool.and_eq_true_iff.mp transition.1).1

theorem RMWTransition64.permissions {memory result : Memory} {event : AtomicEvent64}
    (transition : RMWTransition64 memory event result) :
    result.executable = memory.executable ∧ result.writable = memory.writable := by
  rw [transition.2.2.2]
  exact writeQWord_preserves_permissions ..

/-- Every operand byte was both present and writable before the transition. -/
theorem RMWTransition64.full_permissions {memory result : Memory} {event : AtomicEvent64}
    (transition : RMWTransition64 memory event result) (offset : Nat) (bound : offset < 8) :
    memory.writable (event.address + BitVec.ofNat 64 offset) = true ∧
    (memory.read (event.address + BitVec.ofNat 64 offset)).isSome = true := by
  have allowed := transition.2.1
  simp only [canStoreQWord, qwordWritable, Bool.and_eq_true] at allowed
  obtain ⟨_, writable, readable⟩ := allowed
  have cases : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 ∨
    offset = 4 ∨ offset = 5 ∨ offset = 6 ∨ offset = 7 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, and_self]

/-- Neither equality of old/new values nor a mapped neighbor can authorize a
missing or nonwritable operand byte. Failure exposes no updated memory/event. -/
theorem logicalRmwQWord_denied_byte (op : Sequential.LogicalOp) (memory : Memory)
    (address mask : Word) (offset : Nat) (bound : offset < 8)
    (supported : atomicAddressable64 address = true)
    (denied : memory.writable (address + BitVec.ofNat 64 offset) = false ∨
      memory.read (address + BitVec.ofNat 64 offset) = none) :
    logicalRmwQWord op memory address mask = .error (.writeDenied address) := by
  by_cases allowed : canStoreQWord memory address = true
  · obtain ⟨result, success⟩ := logicalRmwQWord_enabled op memory address mask supported allowed
    have sound := logicalRmwQWord_sound op memory address mask result success
    have permissions := sound.1.full_permissions offset bound
    rw [sound.2.2.2.1] at permissions
    rcases denied with notWritable | missing
    · simp only [notWritable, Bool.false_eq_true, false_and] at permissions
    · simp only [missing, Option.isSome_none, Bool.false_eq_true, and_false] at permissions
  · exact logicalRmwQWord_denied op memory address mask supported (Bool.eq_false_iff.mpr allowed)

theorem RMWTransition64.frame {memory result : Memory} {event : AtomicEvent64}
    (transition : RMWTransition64 memory event result) (query : Word)
    (outside : 8 ≤ (query - event.address).toNat) : result.read query = memory.read query := by
  rw [transition.2.2.2]
  exact writeQWord_frame _ _ _ _ outside

theorem RMWTransition64.preserves_code {memory result : Memory} {event : AtomicEvent64}
    (transition : RMWTransition64 memory event result) (base : Word) (bytes : List Byte)
    (code : CodeAt memory base bytes) (disjoint : QWordDisjoint event.address base bytes.length) :
    CodeAt result base bytes := by
  rw [transition.2.2.2]
  exact writeQWord_preserves_code _ _ _ _ _ code disjoint

/-- Equality of old/new words does not weaken the permission/event contract. -/
theorem logicalRmwQWord_no_change (op : Sequential.LogicalOp) (memory : Memory)
    (address mask old : Word) (supported : atomicAddressable64 address = true)
    (allowed : canStoreQWord memory address = true) (read : loadQWord memory address = .ok old)
    (unchanged : op.eval old mask = old) :
    logicalRmwQWord op memory address mask = .ok
      (writeQWordUnchecked memory address old, ⟨op, mask, ⟨address, old, old⟩⟩) := by
  simpa only [unchanged] using
    logicalRmwQWord_success op memory address mask old supported allowed read

theorem dataOnly64_bytes (memory : Memory) (address : Word)
    (data : dataOnly64 memory address = true) (offset : Nat) (bound : offset < 8) :
    memory.executable (address + BitVec.ofNat 64 offset) = false := by
  simp only [dataOnly64, Bool.and_eq_true, Bool.not_eq_true'] at data
  have cases : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 ∨
    offset = 4 ∨ offset = 5 ∨ offset = 6 ∨ offset = 7 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all only [BitVec.ofNat_eq_ofNat, BitVec.add_zero]

end EDSL.X86
