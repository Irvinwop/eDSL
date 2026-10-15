/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Memory

namespace EDSL.X86
@[simp] theorem throw_error (fault : Error) : (throw fault : Except Error α) = .error fault := rfl

/-- Supported locked ordinary-RAM operand: natural alignment, canonical bytes,
no wrap, no virtual 64-byte-line or 4-KiB-page crossing. Physical interpretation
additionally assumes coherent WB memory and stable translation. Rejection does
not claim that every other hardware XCHG is non-atomic or faults. -/
def atomicAddressable (address : Word) : Bool :=
  dwordAddressable address && decide (address.toNat % 4 = 0 ∧
    address.toNat % 64 + 4 ≤ 64 ∧ address.toNat % 4096 + 4 ≤ 4096)

structure AtomicEvent where
  address : Word
  before : BitVec 32
  after : BitVec 32
  deriving DecidableEq, Repr

/-- One indivisible abstract RMW transition. There is no exposed load/store
intermediate state in this relation. Its conformance to a physical locked
instruction remains an architecture/profile refinement obligation. -/
def ExchangeTransition (memory : Memory) (event : AtomicEvent) (result : Memory) : Prop :=
  atomicAddressable event.address = true ∧ canStoreDWord memory event.address = true ∧
  loadDWord memory event.address = .ok event.before ∧
  result = writeDWordUnchecked memory event.address event.after

def exchangeDWord (memory : Memory) (address : Word) (value : BitVec 32) :
    Except Error (Memory × BitVec 32) := do
  if !atomicAddressable address then throw (.unsupportedAtomicAddress address)
  if !canStoreDWord memory address then throw (.writeDenied address)
  let old ← loadDWord memory address
  return (writeDWordUnchecked memory address value, old)

theorem exchangeDWord_ok (memory : Memory) (address : Word) (value : BitVec 32)
    (result : Memory × BitVec 32) (success : exchangeDWord memory address value = .ok result) :
    ExchangeTransition memory ⟨address, result.2, value⟩ result.1 := by
  by_cases addressValid : atomicAddressable address = true
  · by_cases allowed : canStoreDWord memory address = true
    · cases read : loadDWord memory address with
      | error fault => simp [exchangeDWord, addressValid, allowed, read] at success
      | ok old =>
        simp [exchangeDWord, addressValid, allowed, read] at success
        subst result
        exact ⟨addressValid, allowed, read, rfl⟩
    · simp [exchangeDWord, addressValid, allowed] at success
  · simp [exchangeDWord, addressValid] at success

theorem exchangeDWord_success (memory : Memory) (address : Word) (old value : BitVec 32)
    (supported : atomicAddressable address = true) (allowed : canStoreDWord memory address = true)
    (read : loadDWord memory address = .ok old) :
    exchangeDWord memory address value = .ok (writeDWordUnchecked memory address value, old) := by
  simp [exchangeDWord, supported, allowed, read]

/-- A single indivisible modular fetch-add over the same restricted atomic
RAM profile. The returned word is the observed destination before addition. -/
def fetchAddDWord (memory : Memory) (address : Word) (delta : BitVec 32) :
    Except Error (Memory × BitVec 32) := do
  if !atomicAddressable address then throw (.unsupportedAtomicAddress address)
  if !canStoreDWord memory address then throw (.writeDenied address)
  let old ← loadDWord memory address
  return (writeDWordUnchecked memory address (old + delta), old)

theorem fetchAddDWord_ok (memory : Memory) (address : Word) (delta : BitVec 32)
    (result : Memory × BitVec 32) (success : fetchAddDWord memory address delta = .ok result) :
    ExchangeTransition memory ⟨address, result.2, result.2 + delta⟩ result.1 := by
  by_cases addressValid : atomicAddressable address = true
  · by_cases allowed : canStoreDWord memory address = true
    · cases read : loadDWord memory address with
      | error fault => simp [fetchAddDWord, addressValid, allowed, read] at success
      | ok old =>
        simp [fetchAddDWord, addressValid, allowed, read] at success
        subst result
        exact ⟨addressValid, allowed, read, rfl⟩
    · simp [fetchAddDWord, addressValid, allowed] at success
  · simp [fetchAddDWord, addressValid] at success

theorem fetchAddDWord_success (memory : Memory) (address : Word) (old delta : BitVec 32)
    (supported : atomicAddressable address = true) (allowed : canStoreDWord memory address = true)
    (read : loadDWord memory address = .ok old) :
    fetchAddDWord memory address delta = .ok (writeDWordUnchecked memory address (old + delta), old) := by
  simp [fetchAddDWord, supported, allowed, read]

theorem ExchangeTransition.readback {memory result : Memory} {event : AtomicEvent}
    (transition : ExchangeTransition memory event result) : loadDWord result event.address = .ok event.after := by
  rw [transition.2.2.2]
  exact load_after_write _ _ _ (Bool.and_eq_true_iff.mp transition.1).1

theorem ExchangeTransition.permissions {memory result : Memory} {event : AtomicEvent}
    (transition : ExchangeTransition memory event result) :
    result.executable = memory.executable ∧ result.writable = memory.writable := by
  rw [transition.2.2.2]
  exact ⟨rfl, rfl⟩

theorem ExchangeTransition.frame {memory result : Memory} {event : AtomicEvent}
    (transition : ExchangeTransition memory event result) (query : Word)
    (outside : 4 ≤ (query - event.address).toNat) : result.read query = memory.read query := by
  rw [transition.2.2.2]
  exact writeDWord_frame _ _ _ _ outside

end EDSL.X86
