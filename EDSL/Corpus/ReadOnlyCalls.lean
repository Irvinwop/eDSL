/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.ReadOnlyInputs

set_option autoImplicit false
set_option warningAsError true

/-! Attach one code extent and any finite list of exact input read loans to
an existing manager. The empty placeholder used for code attachment never
consults a data owner, ticket or pointer. No snapshot supplies authority. -/

namespace EDSL.Corpus.ReadOnlyCalls
open X86 OS OS.AddressSpace
open BufferResources (Managed)

structure Attached (before : Managed) (worker : Nat) (code : Region)
    (requests : List ReadOnlyInputs.Request) where
  executable : ReadOnlyResources.Attached before worker code ⟨0, []⟩
  inputs : ReadOnlyInputs.Result executable.managed worker requests

def Attached.managed {before : Managed} {worker : Nat} {code : Region}
    {requests : List ReadOnlyInputs.Request} (result : Attached before worker code requests) : Managed :=
  result.inputs.managed

def Attached.codeLoan {before : Managed} {worker : Nat} {code : Region}
    {requests : List ReadOnlyInputs.Request} (result : Attached before worker code requests) : Nat :=
  result.executable.codeLoan

theorem Attached.codeHeld {before : Managed} {worker : Nat} {code : Region}
    {requests : List ReadOnlyInputs.Request} (result : Attached before worker code requests) :
    Threads.HasLoan result.managed.shared worker result.codeLoan code :=
  result.inputs.original_loan result.executable.codeHeld

theorem Attached.space {before : Managed} {worker : Nat} {code : Region}
    {requests : List ReadOnlyInputs.Request} (result : Attached before worker code requests) :
    result.managed.shared.resources.space = before.shared.resources.space :=
  (congrArg Ownership.World.space result.inputs.resources).trans result.executable.space

theorem Attached.loans {before : Managed} {worker : Nat} {code : Region}
    {requests : List ReadOnlyInputs.Request} (result : Attached before worker code requests)
    (identifier : Nat) (loan : Borrowing.Loan) (live : before.shared.loans identifier = some loan) :
    result.managed.shared.loans identifier = some loan :=
  result.inputs.loans _ _ (result.executable.loans _ _ live)

theorem Attached.allocations {before : Managed} {worker : Nat} {code : Region}
    {requests : List ReadOnlyInputs.Request} (result : Attached before worker code requests)
    (identifier : Nat) (allocation : Ownership.Allocation)
    (live : before.shared.resources.allocations identifier = some allocation) :
    result.managed.shared.resources.allocations identifier = some allocation := by
  change result.inputs.managed.shared.resources.allocations identifier = some allocation
  rw [result.inputs.resources]
  exact result.executable.allocations _ _ live

theorem Attached.history {before : Managed} {worker : Nat} {code : Region}
    {requests : List ReadOnlyInputs.Request} (result : Attached before worker code requests) :
    Borrowing.History before.shared result.managed.shared :=
  ReadOnlyResources.history_trans result.executable.history result.inputs.history

theorem Attached.original_loan {before : Managed} {worker : Nat} {code : Region}
    {requests : List ReadOnlyInputs.Request} (result : Attached before worker code requests)
    {identifier : Nat} {region : Region}
    (original : Threads.HasLoan before.shared worker identifier region) :
    Threads.HasLoan result.managed.shared worker identifier region :=
  result.inputs.original_loan (result.executable.original_loan original)

theorem Attached.authorize {before : Managed} {worker : Nat} {code : Region}
    {requests : List ReadOnlyInputs.Request} (result : Attached before worker code requests)
    {owner : Nat} {ticket : Ownership.Ticket} {allocation : Ownership.Allocation}
    (original : Ownership.authorize before.shared.resources owner ticket = .ok allocation) :
    Ownership.authorize result.managed.shared.resources owner ticket = .ok allocation :=
  result.inputs.authorize (result.executable.authorize original)

/-- Every adoption and positive read borrow is performed by the checked
manager. Empty requests use ReadOnlyInputs' general no-operation branch. -/
def attach (before : Managed) (codeOwner worker : Nat) (code : Region)
    (requests : List ReadOnlyInputs.Request) :
    Except Borrowing.Fault (Attached before worker code requests) := do
  let executable ← ReadOnlyResources.attach before codeOwner 0 ⟨0, 0⟩ worker code ⟨0, []⟩
  let inputs ← ReadOnlyInputs.borrow executable.managed worker requests
  return ⟨executable, inputs⟩

#print axioms attach
#print axioms Attached.codeHeld
#print axioms Attached.space
#print axioms Attached.loans
#print axioms Attached.allocations
#print axioms Attached.history
#print axioms Attached.original_loan
#print axioms Attached.authorize
end EDSL.Corpus.ReadOnlyCalls
#audit_edsl
