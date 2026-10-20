/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.StackFrame.Model

set_option warningAsError true

namespace EDSL.OS.StackFrame
open X86 AddressSpace

/-- Original caller STACK8 uses its retained loan; a private STACK8 uses current
ownership. This is separate from the older CallResources read policy. -/
inductive ReadAllowed (frame : Descriptor) (shared : Shared) (read : Sequential.Read) : Prop where
  | original (allowed : CallResources.ReadAllowed frame.call shared read)
  | privateSlot (kind : read.kind = .stack) (bytes : read.bytes = 8)
      (present : PresentSlot frame shared read.address)

theorem originalStack_readAllowed {frame : Descriptor} {shared : Shared}
    (contract : Contract frame shared) :
    ReadAllowed frame shared ⟨.stack, frame.call.stack, 8⟩ :=
  .original (CallResources.stackRead_permission contract.pureCall)

theorem privateSlot_readAllowed {frame : Descriptor} {shared : Shared} {address : Word}
    (present : PresentSlot frame shared address) : ReadAllowed frame shared ⟨.stack, address, 8⟩ :=
  .privateSlot rfl rfl present

/-- Actual owner read, current owner/epoch authority and actual STACK8 read
follow from present resources. Observation creates no loan or evolved state. -/
theorem PresentSlot.read {frame : Descriptor} {shared : Shared} {address : Word}
    (present : PresentSlot frame shared address) :
    ∃ value, Borrowing.loadOwnedWord64 shared frame.owner frame.ticket address = .ok value ∧
      readWord (toMemory shared.resources.space) address = .ok value ∧
      Ownership.Current shared.resources frame.owner frame.ticket := by
  obtain ⟨allocation, authorized, fits⟩ := present.currentRW.authorize
  obtain ⟨value, read⟩ := Borrowing.loadOwnedWord64_exists _ _ _ _ allocation authorized fits
    present.currentRW.writable
  exact ⟨value, read, Borrowing.loadOwnedWord64_readWord _ _ _ _ _ read,
    Borrowing.loadOwnedWord64_current _ _ _ _ _ read⟩

theorem current_privateSlot {frame : Descriptor} {shared : Shared} {machine : X86.State}
    {address : Word} (current : Current frame shared machine) (slot : Slot frame address) :
    ∃ value, Borrowing.loadOwnedWord64 shared frame.owner frame.ticket address = .ok value ∧
      readWord machine.memory address = .ok value ∧
      Ownership.Current shared.resources frame.owner frame.ticket ∧
      ReadAllowed frame shared ⟨.stack, address, 8⟩ := by
  let present : PresentSlot frame shared address := ⟨current.contract, slot⟩
  obtain ⟨value, read, machineRead, authority⟩ := present.read
  exact ⟨value, read, by rwa [current.coupled], authority, privateSlot_readAllowed present⟩

/-- The retained original contents do not bind a moved RSP to the caller slot. -/
theorem Current.originalStack {frame : Descriptor} {shared : Shared} {machine : X86.State}
    (current : Current frame shared machine) :
    readWord machine.memory frame.call.stack = .ok frame.call.returnAddress := by
  rw [current.coupled]
  exact current.contract.pureCall.stack

end EDSL.OS.StackFrame
