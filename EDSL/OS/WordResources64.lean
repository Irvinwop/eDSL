/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.WordResources
import EDSL.OS.Borrowing.Store64

set_option warningAsError true

namespace EDSL.OS.WordResources64
open EDSL EDSL.X86 EDSL.X86.Sequential EDSL.OS

abbrev Shared := Borrowing.State
abbrev Call := WordResources.Call
abbrev SeqInstruction := EDSL.X86.Sequential.Instruction

/-- Current ownership of one complete readable/writable eight-byte operand
inside a single allocation. Pointer and value widths are both 64 bits. -/
def WordValid (shared : Shared) (owner : Nat) (ticket : Ownership.Ticket)
    (address : Word) : Prop :=
  ∃ allocation, shared.resources.allocations ticket.identifier = some allocation ∧
    allocation.owner = owner ∧ allocation.epoch = ticket.epoch ∧
    Ownership.containsQWord allocation address = true ∧
    canStoreQWord (AddressSpace.toMemory shared.resources.space) address = true

theorem WordValid.authorize {shared : Shared} {owner : Nat}
    {ticket : Ownership.Ticket} {address : Word} (valid : WordValid shared owner ticket address) :
    ∃ allocation, Ownership.authorize shared.resources owner ticket = .ok allocation ∧
      Ownership.containsQWord allocation address = true := by
  obtain ⟨allocation, found, owns, epoch, fits, _⟩ := valid
  exact ⟨allocation, by simp [Ownership.authorize, found, owns, epoch], fits⟩

theorem WordValid.writable {shared : Shared} {owner : Nat}
    {ticket : Ownership.Ticket} {address : Word} (valid : WordValid shared owner ticket address) :
    canStoreQWord (AddressSpace.toMemory shared.resources.space) address = true := by
  obtain ⟨_, _, _, _, _, writable⟩ := valid
  exact writable

theorem WordValid.load_exists {shared : Shared} {owner : Nat}
    {ticket : Ownership.Ticket} {address : Word} (valid : WordValid shared owner ticket address) :
    ∃ value, loadQWord (AddressSpace.toMemory shared.resources.space) address = .ok value :=
  loadQWord_of_canStoreQWord _ _ valid.writable

theorem WordValid.permissions {before after : Shared} {owner : Nat}
    {ticket : Ownership.Ticket} {address : Word}
    (valid : WordValid before owner ticket address)
    (allocations : after.resources.allocations = before.resources.allocations)
    (permissions : ∀ query, (after.resources.space.cells query).map AddressSpace.Cell.permissions =
      (before.resources.space.cells query).map AddressSpace.Cell.permissions) :
    WordValid after owner ticket address := by
  obtain ⟨allocation, found, owns, epoch, fits, writable⟩ := valid
  refine ⟨allocation, by rw [allocations]; exact found, owns, epoch, fits, ?_⟩
  rw [Borrowing.canStoreQWord_permissions permissions]
  exact writable

/-- Allocation identity exclusion supplies an exact eight-byte machine frame,
including loans on a strict subregion of another allocation. -/
theorem word_loan_disjoint {shared : Shared} {owner loanId : Nat}
    {ticket : Ownership.Ticket} {address : Word} {loan : Borrowing.Loan}
    (valid : Borrowing.WellFormed shared)
    (word : WordValid shared owner ticket address)
    (live : shared.loans loanId = some loan)
    (different : ticket.identifier ≠ loan.ticket.identifier) :
    QWordDisjoint address loan.region.base loan.region.length := by
  obtain ⟨allocation, found, _, _, fits, _⟩ := word
  obtain ⟨borrowed, foundBorrowed, _, _, subregion, regionValid, _⟩ := (valid.2 _ _ live).2
  have separate := valid.1.2 _ _ _ _ found foundBorrowed different
  have restricted : Ownership.Disjoint allocation.region loan.region := by
    rcases separate with before | after
    · exact Or.inl (Nat.le_trans before subregion.1)
    · exact Or.inr (Nat.le_trans subregion.2 after)
  have allocationValid := (valid.1.1 _ _ found).2.1
  have bounds : allocation.region.base.toNat ≤ address.toNat ∧
      address.toNat + 8 ≤ allocation.region.base.toNat + allocation.region.length :=
    of_decide_eq_true fits
  have limit := (of_decide_eq_true allocationValid).2.1
  have noWrap : address.toNat + 7 < 2^64 := by omega
  intro offset bound
  have inside : loan.region.Contains (loan.region.base + BitVec.ofNat 64 offset) :=
    Ownership.addresses_inside loan.region regionValid _
      (List.mem_map.mpr ⟨offset, List.mem_range.mpr bound, rfl⟩)
  by_cases outside : 8 ≤ ((loan.region.base + BitVec.ofNat 64 offset) - address).toNat
  · exact outside
  · exact False.elim (Ownership.disjoint_outside restricted inside
      (Ownership.containsQWord_inside allocation address _ fits
        ((AddressSpace.qword_contains_iff address _ noWrap).mpr (by omega))))

theorem word_hasLoan_disjoint {shared : Shared} {owner worker loanId : Nat}
    {ticket : Ownership.Ticket} {address : Word} {region : AddressSpace.Region}
    (valid : Borrowing.WellFormed shared)
    (word : WordValid shared owner ticket address)
    (held : Threads.HasLoan shared worker loanId region)
    (unborrowed : ∀ identifier loan, shared.loans identifier = some loan →
      loan.ticket.identifier ≠ ticket.identifier) :
    QWordDisjoint address region.base region.length := by
  obtain ⟨loan, live, _, sameRegion⟩ := held
  subst region
  exact word_loan_disjoint valid word live (unborrowed _ _ live).symm

/-- Present authority and current cells; there are no future execution or
successful mutation premises. Code and original caller-slot loans are retained
independently of the machine's current RSP register. -/
structure Contract (call : Call) (shared : Shared) : Prop where
  wellFormed : Borrowing.WellFormed shared
  codeLoan : Threads.HasLoan shared call.worker call.codeLoan ⟨call.code, call.bytes.length⟩
  stackLoan : Threads.HasLoan shared call.worker call.stackLoan ⟨call.stack, 8⟩
  code : CodeAt (AddressSpace.toMemory shared.resources.space) call.code call.bytes
  stack : readWord (AddressSpace.toMemory shared.resources.space) call.stack = .ok call.returnAddress
  word : WordValid shared (Threads.principal call.worker) call.ticket call.targetPointer
  unborrowed : ∀ identifier loan, shared.loans identifier = some loan →
    loan.ticket.identifier ≠ call.ticket.identifier
  codeDisjoint : QWordDisjoint call.targetPointer call.code call.bytes.length
  stackDisjoint : QWordDisjoint call.targetPointer call.stack 8
  returnCanonical : canonical call.returnAddress = true
  stackBound : call.stack.toNat + 8 < 2^64
  postStackCanonical : canonical (call.stack + 8) = true

structure Current (call : Call) (shared : Shared) (machine : State) : Prop where
  contract : Contract call shared
  coupled : machine.memory = AddressSpace.toMemory shared.resources.space

/-- Generic transport for register-only MOV/XCHG and other unchanged-memory
states. Retaining the original slot does not supply a new machine RSP binding. -/
theorem Current.sameMemory {call : Call} {shared : Shared} {before after : State}
    (current : Current call shared before) (memory : after.memory = before.memory) :
    Current call shared after := ⟨current.contract, memory.trans current.coupled⟩

def storeAfterLength (before : State) (evolved : Shared) (length : Nat) : State :=
  { before with memory := AddressSpace.toMemory evolved.resources.space
                rip := before.rip + BitVec.ofNat 64 length }

/-- Exact checked 64-bit effect; a missing 32-bit store intent cannot admit it
as a readonly operation. -/
inductive WordEffect (owner : Nat) (ticket : Ownership.Ticket) (targetPointer : Word) :
    Shared → State → SeqInstruction → Observation → Shared → Prop where
  | readOnly {shared before instruction observation}
      (allowed : CFG.readOnly instruction = true) :
      WordEffect owner ticket targetPointer shared before instruction observation shared
  | store64 {shared evolved before instruction observation value}
      (intent : instruction.storeIntent64 before = some (targetPointer, value))
      (success : Borrowing.mutate shared (.store64 owner ticket targetPointer value) = .ok (evolved, none)) :
      WordEffect owner ticket targetPointer shared before instruction observation evolved

/-- Current complete owner authority derives checked Borrowing gate success. -/
theorem current_store64_enabled {call : Call} {shared : Shared} {machine : State}
    (current : Current call shared machine) (value : Word) :
    ∃ evolved, Borrowing.mutate shared
      (.store64 (Threads.principal call.worker) call.ticket call.targetPointer value) = .ok (evolved, none) := by
  obtain ⟨allocation, authorized, fits⟩ := current.contract.word.authorize
  exact Borrowing.store64_admitted _ _ _ _ value allocation authorized fits
    current.contract.word.writable current.contract.unborrowed

/-- A checked OS mutation derives the actual Sequential step, with complete
machine RAM equality rather than agreement only on observed addresses. -/
theorem actual_store64_bridge {shared evolved : Shared} {before : State}
    {instruction : SeqInstruction} {owner : Nat} {ticket : Ownership.Ticket}
    {address value : Word}
    (coupled : before.memory = AddressSpace.toMemory shared.resources.space)
    (decoded : Sequential.decodeAt before = .ok instruction)
    (intent : instruction.storeIntent64 before = some (address, value))
    (success : Borrowing.mutate shared (.store64 owner ticket address value) = .ok (evolved, none))
    (af : Bool) :
    step af before = .ok ⟨.next (storeAfterLength before evolved instruction.length), []⟩ ∧
      Borrowing.StoreEffect64 shared evolved address value := by
  have effect := Borrowing.store64_effect success
  have machine : X86.storeQWord before.memory address value =
      .ok (AddressSpace.toMemory evolved.resources.space) := by
    rw [coupled]
    exact effect.machine
  refine ⟨?_, effect⟩
  rw [step_eq_execute af decoded, execute_storeIntent64 af intent, machine]
  rfl

/-- The checked history preserves every original live loan and its contents,
and all owner/epoch allocation metadata, after the full-width store. -/
theorem contract_store64 {call : Call} {shared evolved : Shared} {value : Word}
    (contract : Contract call shared)
    (success : Borrowing.mutate shared
      (.store64 (Threads.principal call.worker) call.ticket call.targetPointer value) = .ok (evolved, none)) :
    Contract call evolved ∧
      (∀ identifier loan, shared.loans identifier = some loan →
        ∀ query, loan.region.Contains query →
          evolved.resources.space.cells query = shared.resources.space.cells query) := by
  have effect := Borrowing.store64_effect success
  have history : Borrowing.History shared evolved := .next (.mutate success) .refl
  obtain ⟨codeLoan, codeCells⟩ := contract.codeLoan.frame contract.wellFormed history
    (congrFun effect.loans call.codeLoan)
  obtain ⟨stackLoan, stackCells⟩ := contract.stackLoan.frame contract.wellFormed history
    (congrFun effect.loans call.stackLoan)
  refine ⟨?_, ?_⟩
  · exact ⟨history.wellFormed contract.wellFormed, codeLoan, stackLoan,
      AddressSpace.agrees_code _ _ _ _ codeCells contract.code,
      (readWord_congr _ _ _ (AddressSpace.agrees_read _ _ _ _ stackCells)).trans contract.stack,
      contract.word.permissions effect.allocations effect.permissions,
      fun identifier loan live => contract.unborrowed identifier loan (by rwa [← effect.loans]),
      contract.codeDisjoint, contract.stackDisjoint, contract.returnCanonical,
      contract.stackBound, contract.postStackCanonical⟩
  · intro identifier loan live query inside
    have below := (contract.wellFormed.2 identifier loan live).1
    exact (history.loan_stable contract.wellFormed identifier below loan
      ((congrFun effect.loans identifier).trans live)).2 query inside

/-- Present resources and a decoded full64 store intent produce one concrete
world shared by checked OS mutation, actual machine execution and its complete
readback/frame. No successful future OS result is assumed. -/
theorem current_store64_step {call : Call} {shared : Shared} {before : State}
    {instruction : SeqInstruction} {value : Word}
    (current : Current call shared before)
    (decoded : Sequential.decodeAt before = .ok instruction)
    (intent : instruction.storeIntent64 before = some (call.targetPointer, value)) (af : Bool) :
    ∃ evolved,
      Borrowing.mutate shared (.store64 (Threads.principal call.worker) call.ticket call.targetPointer value) =
        .ok (evolved, none) ∧
      step af before = .ok ⟨.next (storeAfterLength before evolved instruction.length), []⟩ ∧
      Current call evolved (storeAfterLength before evolved instruction.length) ∧
      Borrowing.StoreEffect64 shared evolved call.targetPointer value ∧
      (∀ identifier loan, shared.loans identifier = some loan →
        ∀ query, loan.region.Contains query →
          evolved.resources.space.cells query = shared.resources.space.cells query) := by
  obtain ⟨evolved, stored⟩ := current_store64_enabled current value
  obtain ⟨actual, effect⟩ := actual_store64_bridge current.coupled decoded intent stored af
  obtain ⟨contract, loans⟩ := contract_store64 current.contract stored
  exact ⟨evolved, stored, actual, ⟨contract, rfl⟩, effect, loans⟩

/-- A target read uses the current complete owner allocation; a caller-stack
read uses its original eight-byte loan. No target loan is created. -/
def ReadAllowed (call : Call) (shared : Shared) (before : State) (read : Read) : Prop :=
  match read.kind with
  | .stack => read.address = call.stack ∧ read.bytes = 8 ∧
      ArrayResources.ReadPermission shared call.worker read
  | .data => read.address = call.targetPointer ∧ read.bytes = 8 ∧
      ∃ allocation value,
        Ownership.authorize shared.resources (Threads.principal call.worker) call.ticket = .ok allocation ∧
        Ownership.containsQWord allocation call.targetPointer = true ∧
        loadQWord before.memory call.targetPointer = .ok value

/-- The actual pre-state supplies the full address even when the destination
aliases its base/index. Loading RSP retains the original caller loan; a RET
still needs the separate binding to that original address. -/
theorem current_load64_step {call : Call} {shared : Shared} {before : State}
    {destination : Register} {address : Address}
    (current : Current call shared before)
    (decoded : Sequential.decodeAt before = .ok (.loadMem64 destination address))
    (effective : address.eval before = call.targetPointer) (af : Bool) :
    ∃ (value : Word) (after : State),
      step af before = .ok ⟨.next after, [⟨.data, call.targetPointer, 8⟩]⟩ ∧
      after.registers destination = value ∧
      loadQWord before.memory call.targetPointer = .ok value ∧
      ReadAllowed call shared before ⟨.data, call.targetPointer, 8⟩ ∧
      OperandReadSucceeds before ⟨.data, call.targetPointer, 8⟩ ∧
      Current call shared after ∧
      (∀ register, register ≠ destination → after.registers register = before.registers register) ∧
      after.memory = before.memory ∧ after.flags = before.flags ∧
      after.rip = before.rip + BitVec.ofNat 64 (Sequential.Instruction.loadMem64 destination address).length := by
  obtain ⟨allocation, authorized, fits⟩ := current.contract.word.authorize
  obtain ⟨value, observed⟩ := current.contract.word.load_exists
  have loaded : loadQWord before.memory call.targetPointer = .ok value := by
    rw [current.coupled]
    exact observed
  let after : State := { before.writeRegister destination value with
    rip := before.rip + BitVec.ofNat 64 (Sequential.Instruction.loadMem64 destination address).length }
  refine ⟨value, after, ?_, ?_, loaded, ⟨rfl, rfl, allocation, value, authorized, fits, loaded⟩,
    ?_, ⟨current.contract, current.coupled⟩, ?_, rfl, rfl, rfl⟩
  · rw [step_eq_execute af decoded]
    simp only [execute_loadMem64, effective, loaded, ok_bind, pure_ok, after]
  · simp [after, State.writeRegister]
  · exact ⟨value, loaded⟩
  · intro register different
    simp [after, State.writeRegister, different]

/-- Readonly transport retains the same present world and original loans. -/
theorem current_readOnly_step {call : Call} {shared : Shared} {before : State}
    {instruction : SeqInstruction} {af : Bool} {observation : Observation}
    (current : Current call shared before)
    (decoded : Sequential.decodeAt before = .ok instruction)
    (allowed : CFG.readOnly instruction = true)
    (actual : step af before = .ok observation) :
    ∃ after, (observation.result = .next after ∨ observation.result = .returned after) ∧
      Current call shared after := by
  have executed : execute before instruction af = .ok observation := by
    rw [← step_eq_execute af decoded]
    exact actual
  obtain ⟨after, next | ⟨returned, _⟩⟩ := CFG.execute_result allowed executed
  · exact ⟨after, Or.inl next, current.sameMemory (CFG.execute_next_memory allowed executed next)⟩
  · exact ⟨after, Or.inr returned, current.sameMemory (CFG.execute_returned_memory allowed executed returned)⟩

end EDSL.OS.WordResources64
