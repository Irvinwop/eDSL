/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.BufferResources

set_option autoImplicit false
set_option warningAsError true

/-! Extend an existing checked manager with another code allocation and exact
read-only input authority. Adoption and shared borrowing preserve the complete
space and every original loan; no RAM authority is supplied by a snapshot. -/

namespace EDSL.Corpus.ReadOnlyResources
open X86 OS OS.AddressSpace
open BufferResources (Managed)

/-- A computational view of the SAME manager, justified by equality of the
entire space. This neither adds an allocation nor changes authority. -/
def reindex (before : Managed) (space : Space)
    (same : space = before.shared.resources.space) : Managed :=
  ⟨{ before.shared with resources := { before.shared.resources with space := space } },
    by simpa only [same] using before.valid⟩

theorem reindex_shared (before : Managed) (space : Space)
    (same : space = before.shared.resources.space) :
    (reindex before space same).shared = before.shared := by
  simp only [reindex, same]

private theorem adopt_frame {before after : Borrowing.State} {owner : Nat}
    {region : Region} {ticket : Option Ownership.Ticket}
    (valid : Borrowing.WellFormed before)
    (success : Borrowing.mutate before (.adopt owner region) = .ok (after, ticket)) :
    after.resources.space = before.resources.space ∧ after.loans = before.loans := by
  obtain ⟨_, resources, changed, same⟩ := Borrowing.mutate_ok _ _ _ success
  cases adopted : Ownership.adopt before.resources owner region with
  | error fault => simp [Ownership.Mutation.run, adopted, Except.map] at changed
  | ok result =>
    have equal : (result.1, some result.2) = resources := by
      simpa [Ownership.Mutation.run, adopted, Except.map] using changed
    subst resources
    cases same
    exact ⟨(Ownership.adopt_wellFormed _ _ _ _ valid.1 adopted).2.2.1, rfl⟩

private theorem adopt_allocations {before after : Borrowing.State} {owner : Nat}
    {region : Region} {ticket : Option Ownership.Ticket}
    (valid : Borrowing.WellFormed before)
    (success : Borrowing.mutate before (.adopt owner region) = .ok (after, ticket)) :
    ∀ identifier allocation, before.resources.allocations identifier = some allocation →
      after.resources.allocations identifier = some allocation := by
  obtain ⟨_, resources, changed, same⟩ := Borrowing.mutate_ok _ _ _ success
  cases same
  intro identifier allocation found
  exact (Ownership.Mutation.run_preserves (.adopt owner region) _ _ identifier valid.1 changed
    (by intro impossible; cases impossible) allocation found).1

structure Adopted (before : Managed) where
  managed : Managed
  ticket : Ownership.Ticket
  space : managed.shared.resources.space = before.shared.resources.space
  loans : managed.shared.loans = before.shared.loans
  allocations : ∀ identifier allocation, before.shared.resources.allocations identifier = some allocation →
    managed.shared.resources.allocations identifier = some allocation
  history : Borrowing.History before.shared managed.shared

def adopt (before : Managed) (owner : Nat) (region : Region) :
    Except Borrowing.Fault (Adopted before) :=
  match success : Borrowing.mutate before.shared (.adopt owner region) with
  | .error fault => .error fault
  | .ok (_, none) => .error (.ownership .missingAllocation)
  | .ok (after, some ticket) =>
    .ok ⟨⟨after, Borrowing.mutate_wellFormed _ _ _ before.valid success⟩, ticket,
      (adopt_frame before.valid success).1, (adopt_frame before.valid success).2,
      adopt_allocations before.valid success,
      .next (.mutate success) .refl⟩

structure Borrowed (before : Managed) (worker : Nat) (region : Region) where
  managed : Managed
  identifier : Nat
  held : Threads.HasLoan managed.shared worker identifier region
  space : managed.shared.resources.space = before.shared.resources.space
  loans : ∀ identifier loan, before.shared.loans identifier = some loan →
    managed.shared.loans identifier = some loan
  resources : managed.shared.resources = before.shared.resources
  history : Borrowing.History before.shared managed.shared

def borrow (before : Managed) (owner : Nat) (ticket : Ownership.Ticket)
    (worker : Nat) (region : Region) : Except Borrowing.Fault (Borrowed before worker region) :=
  match success : Borrowing.readBorrow before.shared owner ticket (Threads.principal worker) region with
  | .error fault => .error fault
  | .ok result =>
    have facts := Borrowing.readBorrow_wellFormed _ _ _ _ _ _ before.valid success
    have shape : result = (Borrowing.installLoan before.shared
        ⟨ticket, owner, Threads.principal worker, region⟩, before.shared.nextLoan) := by
      obtain ⟨_, _, _, _, _, same⟩ := Borrowing.readBorrow_ok _ _ _ _ _ _ success
      exact same
    .ok ⟨⟨result.1, facts.1⟩, result.2, ⟨_, facts.2, rfl, rfl⟩,
      by change result.1.resources.space = _; simp only [shape, Borrowing.installLoan],
      by
        intro identifier loan live
        change result.1.loans identifier = some loan
        have below := (before.valid.2 identifier loan live).1
        have different : identifier ≠ before.shared.nextLoan := by omega
        simpa only [shape, Borrowing.installLoan, ite_eq_right different] using live,
      by change result.1.resources = _; simp only [shape, Borrowing.installLoan],
      .next (.readBorrow success) .refl⟩

/-- Input borrowing, unlike a padded allocation, uses the exact positive byte
extent. Empty buffers leave the manager and unused identifier untouched. -/
def borrowBuffer (before : Managed) (owner : Nat) (ticket : Ownership.Ticket)
    (worker : Nat) (buffer : BufferCall.Buffer) (unused : Nat := 0) :
    Except Borrowing.Fault (Managed × Nat) := do
  if buffer.bytes = [] then return (before, unused)
  let result ← borrow before owner ticket worker buffer.region
  return (result.managed, result.identifier)

theorem borrowBuffer_empty (before : Managed) (owner worker unused : Nat)
    (ticket : Ownership.Ticket) (base : Word) :
    borrowBuffer before owner ticket worker ⟨base, []⟩ unused = .ok (before, unused) := rfl

structure Attached (before : Managed) (worker : Nat) (code : Region) (buffer : BufferCall.Buffer) where
  managed : Managed
  codeLoan : Nat
  inputLoan : Nat
  codeHeld : Threads.HasLoan managed.shared worker codeLoan code
  inputHeld : buffer.bytes ≠ [] → Threads.HasLoan managed.shared worker inputLoan buffer.region
  space : managed.shared.resources.space = before.shared.resources.space
  loans : ∀ identifier loan, before.shared.loans identifier = some loan →
    managed.shared.loans identifier = some loan
  allocations : ∀ identifier allocation, before.shared.resources.allocations identifier = some allocation →
    managed.shared.resources.allocations identifier = some allocation
  history : Borrowing.History before.shared managed.shared

theorem history_trans {before middle after : Borrowing.State}
    (first : Borrowing.History before middle) (last : Borrowing.History middle after) :
    Borrowing.History before after := by
  induction first with
  | refl => exact last
  | next head _ tail => exact .next head (tail last)

/-- All ownership and loan changes are checked Borrowing actions. The original
caller record is retained, never replaced with a new return-slot loan. -/
def attach (before : Managed) (codeOwner dataOwner : Nat) (dataTicket : Ownership.Ticket)
    (worker : Nat) (code : Region) (buffer : BufferCall.Buffer) (unused : Nat := 0) :
    Except Borrowing.Fault (Attached before worker code buffer) := do
  let registered ← adopt before codeOwner code
  let executable ← borrow registered.managed codeOwner registered.ticket worker code
  if empty : buffer.bytes = [] then
    return ⟨executable.managed, executable.identifier, unused, executable.held,
      fun nonempty => False.elim (nonempty empty),
      executable.space.trans registered.space,
      fun identifier loan live => executable.loans identifier loan (registered.loans.symm ▸ live),
      fun identifier allocation found => by
        rw [executable.resources]
        exact registered.allocations identifier allocation found,
      history_trans registered.history executable.history⟩
  else
    let input ← borrow executable.managed dataOwner dataTicket worker buffer.region
    return ⟨input.managed, executable.identifier, input.identifier,
      by
        obtain ⟨loan, live, borrower, region⟩ := executable.held
        exact ⟨loan, input.loans _ _ live, borrower, region⟩,
      fun _ => input.held, input.space.trans (executable.space.trans registered.space),
      fun identifier loan live => input.loans identifier loan
        (executable.loans identifier loan (registered.loans.symm ▸ live)),
      fun identifier allocation found => by
        rw [input.resources, executable.resources]
        exact registered.allocations identifier allocation found,
      history_trans registered.history (history_trans executable.history input.history)⟩

theorem Attached.original_loan {before : Managed} {worker : Nat} {code : Region}
    {buffer : BufferCall.Buffer} (attached : Attached before worker code buffer)
    {identifier : Nat} {region : Region}
    (original : Threads.HasLoan before.shared worker identifier region) :
    Threads.HasLoan attached.managed.shared worker identifier region := by
  obtain ⟨loan, live, borrower, same⟩ := original
  exact ⟨loan, attached.loans _ _ live, borrower, same⟩

theorem Attached.frame {before : Managed} {worker : Nat} {code : Region}
    {buffer : BufferCall.Buffer} (attached : Attached before worker code buffer)
    (address : Word) :
    attached.managed.shared.resources.space.cells address = before.shared.resources.space.cells address :=
  congrArg (fun space : Space => space.cells address) attached.space

theorem Attached.authorize {before : Managed} {worker : Nat} {code : Region}
    {buffer : BufferCall.Buffer} (attached : Attached before worker code buffer)
    {owner : Nat} {ticket : Ownership.Ticket} {allocation : Ownership.Allocation}
    (original : Ownership.authorize before.shared.resources owner ticket = .ok allocation) :
    Ownership.authorize attached.managed.shared.resources owner ticket = .ok allocation := by
  obtain ⟨found, owns, epoch⟩ := Ownership.authorize_ok _ _ _ _ original
  exact Ownership.authorize_success _ _ _ _ (attached.allocations _ _ found) owns epoch

#print axioms attach
#print axioms Attached.original_loan
#print axioms Attached.frame
#print axioms Attached.authorize
end EDSL.Corpus.ReadOnlyResources
#audit_edsl
