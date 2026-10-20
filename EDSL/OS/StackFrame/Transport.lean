/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.StackFrame.History

set_option warningAsError true

namespace EDSL.OS.StackFrame
open X86 AddressSpace

/-- Transport current stack authority through a real checked history. External
owned stores are allowed: the premise retains metadata and permissions, while
loan stability follows from the checked history rather than a private RAM frame. -/
theorem Contract.transport {frame : Descriptor} {before after : Shared}
    (contract : Contract frame before) (history : Borrowing.History before after)
    (allocations : after.resources.allocations = before.resources.allocations)
    (permissions : ∀ query, (after.resources.space.cells query).map Cell.permissions =
      (before.resources.space.cells query).map Cell.permissions)
    (loans : after.loans = before.loans) : Contract frame after := by
  obtain ⟨codeLoan, codeCells⟩ := contract.pureCall.codeLoan.frame contract.wellFormed history
    (congrFun loans frame.call.codeLoan)
  obtain ⟨stackLoan, stackCells⟩ := contract.pureCall.stackLoan.frame contract.wellFormed history
    (congrFun loans frame.call.stackLoan)
  have pureCall : CallResources.Contract frame.call after :=
    ⟨history.wellFormed contract.wellFormed, codeLoan, stackLoan,
      AddressSpace.agrees_code _ _ _ _ codeCells contract.pureCall.code,
      (readWord_congr _ _ _ (AddressSpace.agrees_read _ _ _ _ stackCells)).trans
        contract.pureCall.stack,
      contract.pureCall.returnCanonical, contract.pureCall.stackBound,
      contract.pureCall.postStackCanonical⟩
  obtain ⟨allocation, authorized, region⟩ := contract.allocation
  refine ⟨pureCall, ⟨allocation, ?_, region⟩, contract.topBound,
    fun query slot => (contract.ready query slot).permissions allocations permissions,
    fun identifier loan live => contract.unborrowed identifier loan (by rwa [← loans])⟩
  simpa only [Ownership.authorize, allocations] using authorized

end EDSL.OS.StackFrame
