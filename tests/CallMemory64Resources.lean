/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.CallMemory64.History
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.CallMemory64Resources
open X86 OS AddressSpace

/-- Independent endpoint observations after two real mutations exercise the
shared-world composition: a private write must retain the preceding DATA value,
while both capabilities remain usable. Values, input memory and slot are arbitrary. -/
theorem alternating_stores {descriptor : CallMemory64.Descriptor}
    {shared : Borrowing.State} {machine : X86.State} {address : Word}
    (current : CallMemory64.Current descriptor shared machine)
    (slot : StackFrame.Slot descriptor.frame address) (dataValue privateValue : Word) :
    ∃ middle after,
      Borrowing.mutate shared
        (.store64 descriptor.owner descriptor.ticket descriptor.target dataValue) =
          .ok (middle, none) ∧
      Borrowing.mutate middle
        (.store64 descriptor.owner descriptor.frame.ticket address privateValue) =
          .ok (after, none) ∧
      readWord (toMemory after.resources.space) descriptor.target = .ok dataValue ∧
      readWord (toMemory after.resources.space) address = .ok privateValue ∧
      CallMemory64.Contract descriptor after ∧
      CallMemory64.Preservation descriptor shared after := by
  obtain ⟨middle, storedData, middleCurrent, dataWrite, _, dataRead, _⟩ :=
    current.data_store64 dataValue
  obtain ⟨after, storedPrivate, finalCurrent, privateWrite, _, _, privateRead⟩ :=
    middleCurrent.private_store64 slot privateValue
  have retained := CallMemory64.private_store64_preserves_data middleCurrent.contract slot
    storedPrivate dataRead
  exact ⟨middle, after, storedData, storedPrivate,
    Borrowing.loadOwnedWord64_readWord _ _ _ _ _ retained, privateRead,
    finalCurrent.contract, dataWrite.preserves.trans privateWrite.preserves⟩

end EDSL.Tests.CallMemory64Resources

#print axioms EDSL.Tests.CallMemory64Resources.alternating_stores
#audit_edsl
