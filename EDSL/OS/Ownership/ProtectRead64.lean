/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Ownership.Lifetime

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.OS.Ownership
open X86 AddressSpace

private theorem protect_readable_byte {space : Space} {region : Region}
    {permissions : Permissions} (readable : permissions.readable = true)
    {address : Word} {byte : Byte}
    (observed : (toMemory space).read address = some byte) :
    (toMemory (protectUnchecked space region permissions)).read address = some byte := by
  by_cases inside : region.Contains address
  · cases stored : space.cells address with
    | none => simp [toMemory, stored] at observed
    | some cell =>
      cases oldReadable : cell.permissions.readable with
      | false => simp [toMemory, stored, oldReadable] at observed
      | true =>
        have same : cell.byte = byte := by
          simpa [toMemory, stored, oldReadable] using observed
        simp [toMemory, protectUnchecked, inside, stored, readable, same]
  · simpa only [toMemory, protectUnchecked, ite_eq_right inside] using observed

private theorem protect_readable_dataByte {space : Space} {region : Region}
    {permissions : Permissions} (readable : permissions.readable = true)
    {address : Word} {byte : Byte}
    (observed : readDataByte (toMemory space) address = .ok byte) :
    readDataByte (toMemory (protectUnchecked space region permissions)) address = .ok byte := by
  by_cases canonical : X86.canonical address = true
  · cases fetched : (toMemory space).read address with
    | none => simp [readDataByte, canonical, fetched] at observed
    | some actual =>
      have same : actual = byte := by
        simpa [readDataByte, canonical, fetched] using observed
      have final := protect_readable_byte (region := region) (permissions := permissions) readable fetched
      simp [readDataByte, canonical, final, same]
  · simp [readDataByte, canonical] at observed

private theorem bind_success_iff {ε α β : Type} (result : Except ε α)
    (next : α → Except ε β) (value : β) :
    (result >>= next) = .ok value ↔
      ∃ input, result = .ok input ∧ next input = .ok value := by
  cases result <;> simp

private theorem machineThrow_error {α : Type} (fault : X86.Error) :
    (throw fault : Except X86.Error α) = .error fault := rfl

/-- Enabling reads while retaining every byte preserves an already successful
complete qword observation, including its canonicality and nonwrapping checks.
No write permission, allocation containment, or expected-value test is added. -/
theorem protectUnchecked_readback {space : Space} {region : Region}
    {permissions : Permissions} (readable : permissions.readable = true)
    {address value : Word}
    (observed : loadQWord (toMemory space) address = .ok value) :
    loadQWord (toMemory (protectUnchecked space region permissions)) address = .ok value := by
  by_cases wraps : address.toNat + 7 ≥ 2^64
  · simp [loadQWord, wraps, machineThrow_error] at observed
  · simp only [loadQWord, ite_eq_right wraps, bind_success_iff] at observed ⊢
    obtain ⟨b0, at0, b1, at1, b2, at2, b3, at3,
      b4, at4, b5, at5, b6, at6, b7, at7, joined⟩ := observed
    exact ⟨b0, protect_readable_dataByte readable at0,
      b1, protect_readable_dataByte readable at1,
      b2, protect_readable_dataByte readable at2,
      b3, protect_readable_dataByte readable at3,
      b4, protect_readable_dataByte readable at4,
      b5, protect_readable_dataByte readable at5,
      b6, protect_readable_dataByte readable at6,
      b7, protect_readable_dataByte readable at7, joined⟩

/-- A real successful protection to read-only retains the actual qword read.
The authority and address-space checks are those of `Ownership.protect`. -/
theorem protect_readback {before after : World} {owner : Nat} {ticket : Ticket}
    {address value : Word}
    (changed : protect before owner ticket readOnly = .ok after)
    (observed : loadQWord (toMemory before.space) address = .ok value) :
    loadQWord (toMemory after.space) address = .ok value := by
  obtain ⟨allocation, space, _, protection, shape⟩ := protect_ok _ _ _ _ _ changed
  have spaceEq := (AddressSpace.protect_ok _ _ _ _ protection).1
  simpa only [shape, spaceEq] using
    protectUnchecked_readback (region := allocation.region) (permissions := readOnly) rfl observed

end EDSL.OS.Ownership
