/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.AtomicMemory64

namespace EDSL.X86

/-- A full-width arithmetic RMW event. The argument is retained even when the
sum is unchanged; the old value is the fetch-add response. -/
structure FetchAddEvent64 where
  delta : Word
  event : AtomicEvent64
  deriving DecidableEq, Repr

/-- Full eight-byte preflight and one abstract indivisible arithmetic update.
The sum is modulo 2^64. Failure returns only the error, with no partial memory
or event. Even delta zero requires every current byte to be readable/writable.

This memory primitive does not decode XADD, change registers/flags, provide OS
resource authority, schedule threads or prove linearizability. It inherits the
explicit abstract/physical boundary of `atomicAddressable64`. `dataOnly64` is an
additional fixed-code execution gate for callers, not an ordinary RAM permission
and not imposed by this primitive. -/
def fetchAddQWord (memory : Memory) (address delta : Word) :
    Except Error (Memory × FetchAddEvent64) := do
  if !atomicAddressable64 address then throw (.unsupportedAtomicAddress address)
  if !canStoreQWord memory address then throw (.writeDenied address)
  let old ← loadQWord memory address
  let value := old + delta
  return (writeQWordUnchecked memory address value, ⟨delta, ⟨address, old, value⟩⟩)

theorem fetchAddQWord_sound (memory : Memory) (address delta : Word)
    (result : Memory × FetchAddEvent64)
    (success : fetchAddQWord memory address delta = .ok result) :
    RMWTransition64 memory result.2.event result.1 ∧ result.2.delta = delta ∧
    result.2.event.address = address ∧
    result.2.event.after = result.2.event.before + delta := by
  by_cases supported : atomicAddressable64 address = true
  · by_cases allowed : canStoreQWord memory address = true
    · cases read : loadQWord memory address with
      | error fault => simp [fetchAddQWord, supported, allowed, read] at success
      | ok old =>
        simp [fetchAddQWord, supported, allowed, read] at success
        subst result
        exact ⟨⟨supported, allowed, read, rfl⟩, rfl, rfl, rfl⟩
    · simp [fetchAddQWord, supported, allowed] at success
  · simp [fetchAddQWord, supported] at success

/-- Independent natural-number characterization of the arithmetic result. -/
theorem fetchAddQWord_modular (memory : Memory) (address delta : Word)
    (result : Memory × FetchAddEvent64)
    (success : fetchAddQWord memory address delta = .ok result) :
    result.2.event.after.toNat = (result.2.event.before.toNat + delta.toNat) % 2^64 := by
  rw [(fetchAddQWord_sound memory address delta result success).2.2.2]
  exact BitVec.toNat_add _ _

theorem fetchAddQWord_success (memory : Memory) (address delta old : Word)
    (supported : atomicAddressable64 address = true)
    (allowed : canStoreQWord memory address = true)
    (read : loadQWord memory address = .ok old) :
    fetchAddQWord memory address delta = .ok
      (writeQWordUnchecked memory address (old + delta), ⟨delta, ⟨address, old, old + delta⟩⟩) := by
  simp [fetchAddQWord, supported, allowed, read]

theorem fetchAddQWord_enabled (memory : Memory) (address delta : Word)
    (supported : atomicAddressable64 address = true)
    (allowed : canStoreQWord memory address = true) :
    ∃ result, fetchAddQWord memory address delta = .ok result := by
  obtain ⟨old, read⟩ := loadQWord_of_canStoreQWord memory address allowed
  exact ⟨_, fetchAddQWord_success memory address delta old supported allowed read⟩

theorem fetchAddQWord_enabled_iff (memory : Memory) (address delta : Word) :
    (∃ result, fetchAddQWord memory address delta = .ok result) ↔
      atomicAddressable64 address = true ∧ canStoreQWord memory address = true := by
  constructor
  · rintro ⟨result, success⟩
    have sound := fetchAddQWord_sound memory address delta result success
    rw [← sound.2.2.1]
    exact ⟨sound.1.1, sound.1.2.1⟩
  · rintro ⟨supported, allowed⟩
    exact fetchAddQWord_enabled memory address delta supported allowed

theorem fetchAddQWord_unsupported (memory : Memory) (address delta : Word)
    (unsupported : atomicAddressable64 address = false) :
    fetchAddQWord memory address delta = .error (.unsupportedAtomicAddress address) := by
  simp [fetchAddQWord, unsupported]

theorem fetchAddQWord_denied (memory : Memory) (address delta : Word)
    (supported : atomicAddressable64 address = true)
    (denied : canStoreQWord memory address = false) :
    fetchAddQWord memory address delta = .error (.writeDenied address) := by
  simp [fetchAddQWord, supported, denied]

/-- The complete failure classification. Failed validation never exposes a
replacement memory/event pair, nor a later per-byte read fault. -/
theorem fetchAddQWord_error_iff (memory : Memory) (address delta : Word) (fault : Error) :
    fetchAddQWord memory address delta = .error fault ↔
      (atomicAddressable64 address = false ∧ fault = .unsupportedAtomicAddress address) ∨
      (atomicAddressable64 address = true ∧ canStoreQWord memory address = false ∧
        fault = .writeDenied address) := by
  by_cases supported : atomicAddressable64 address = true
  · by_cases allowed : canStoreQWord memory address = true
    · obtain ⟨result, success⟩ := fetchAddQWord_enabled memory address delta supported allowed
      simp [success, supported, allowed]
    · have denied := Bool.eq_false_iff.mpr allowed
      rw [fetchAddQWord_denied memory address delta supported denied]
      constructor
      · intro failed
        exact Or.inr ⟨supported, denied, (Except.error.inj failed).symm⟩
      · rintro (⟨contradiction, _⟩ | ⟨_, _, rfl⟩)
        · simp only [supported, Bool.true_eq_false] at contradiction
        · rfl
  · have unsupported := Bool.eq_false_iff.mpr supported
    rw [fetchAddQWord_unsupported memory address delta unsupported]
    constructor
    · intro failed
      exact Or.inl ⟨unsupported, (Except.error.inj failed).symm⟩
    · rintro (⟨_, rfl⟩ | ⟨contradiction, _, _⟩)
      · rfl
      · simp only [unsupported, Bool.false_eq_true] at contradiction

/-- The response is the complete value read from current memory. -/
theorem fetchAddQWord_old (memory : Memory) (address delta : Word)
    (result : Memory × FetchAddEvent64)
    (success : fetchAddQWord memory address delta = .ok result) :
    loadQWord memory address = .ok result.2.event.before := by
  have sound := fetchAddQWord_sound memory address delta result success
  rw [← sound.2.2.1]
  exact sound.1.2.2.1

theorem fetchAddQWord_readback (memory : Memory) (address delta : Word)
    (result : Memory × FetchAddEvent64)
    (success : fetchAddQWord memory address delta = .ok result) :
    loadQWord result.1 address = .ok result.2.event.after := by
  have sound := fetchAddQWord_sound memory address delta result success
  rw [← sound.2.2.1]
  exact sound.1.readback

theorem fetchAddQWord_permissions (memory : Memory) (address delta : Word)
    (result : Memory × FetchAddEvent64)
    (success : fetchAddQWord memory address delta = .ok result) :
    result.1.executable = memory.executable ∧ result.1.writable = memory.writable := by
  exact (fetchAddQWord_sound memory address delta result success).1.permissions

theorem fetchAddQWord_full_permissions (memory : Memory) (address delta : Word)
    (result : Memory × FetchAddEvent64)
    (success : fetchAddQWord memory address delta = .ok result)
    (offset : Nat) (bound : offset < 8) :
    memory.writable (address + BitVec.ofNat 64 offset) = true ∧
    (memory.read (address + BitVec.ofNat 64 offset)).isSome = true := by
  have sound := fetchAddQWord_sound memory address delta result success
  rw [← sound.2.2.1]
  exact sound.1.full_permissions offset bound

theorem fetchAddQWord_denied_byte (memory : Memory) (address delta : Word)
    (offset : Nat) (bound : offset < 8)
    (supported : atomicAddressable64 address = true)
    (denied : memory.writable (address + BitVec.ofNat 64 offset) = false ∨
      memory.read (address + BitVec.ofNat 64 offset) = none) :
    fetchAddQWord memory address delta = .error (.writeDenied address) := by
  by_cases allowed : canStoreQWord memory address = true
  · obtain ⟨result, success⟩ := fetchAddQWord_enabled memory address delta supported allowed
    have permissions := fetchAddQWord_full_permissions memory address delta result success offset bound
    rcases denied with notWritable | missing
    · simp only [notWritable, Bool.false_eq_true, false_and] at permissions
    · simp only [missing, Option.isSome_none, Bool.false_eq_true, and_false] at permissions
  · exact fetchAddQWord_denied memory address delta supported (Bool.eq_false_iff.mpr allowed)

theorem fetchAddQWord_frame (memory : Memory) (address delta : Word)
    (result : Memory × FetchAddEvent64)
    (success : fetchAddQWord memory address delta = .ok result) (query : Word)
    (outside : 8 ≤ (query - address).toNat) : result.1.read query = memory.read query := by
  have sound := fetchAddQWord_sound memory address delta result success
  apply sound.1.frame query
  simpa only [sound.2.2.1] using outside

theorem fetchAddQWord_preserves_code (memory : Memory) (address delta : Word)
    (result : Memory × FetchAddEvent64)
    (success : fetchAddQWord memory address delta = .ok result) (base : Word) (bytes : List Byte)
    (code : CodeAt memory base bytes) (disjoint : QWordDisjoint address base bytes.length) :
    CodeAt result.1 base bytes := by
  have sound := fetchAddQWord_sound memory address delta result success
  apply sound.1.preserves_code base bytes code
  simpa only [sound.2.2.1] using disjoint

/-- Zero remains an authorized full-width RMW, carrying an actual old value
and a zero delta event; permission requirements do not disappear. -/
theorem fetchAddQWord_zero (memory : Memory) (address old : Word)
    (supported : atomicAddressable64 address = true)
    (allowed : canStoreQWord memory address = true)
    (read : loadQWord memory address = .ok old) :
    fetchAddQWord memory address 0 = .ok
      (writeQWordUnchecked memory address old, ⟨0, ⟨address, old, old⟩⟩) := by
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
    fetchAddQWord_success memory address 0 old supported allowed read

end EDSL.X86
