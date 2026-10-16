/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.CFGTransport
import EDSL.OS.ArrayResources
import EDSL.OS.Mutex.Memory
import EDSL.OS.Mutex.Enabled

set_option warningAsError true

namespace EDSL.OS.WordResources
open EDSL EDSL.X86 EDSL.X86.Sequential EDSL.OS

abbrev Shared := Borrowing.State
abbrev SeqInstruction := EDSL.X86.Sequential.Instruction

/-- Immutable resource handles. The current OS state is a separate argument. -/
structure Call where
  worker : Nat
  ticket : Ownership.Ticket
  targetPointer : Word
  code : Word
  stack : Word
  returnAddress : Word
  bytes : List Byte
  codeLoan : Nat
  stackLoan : Nat

/-- Allocation identity exclusion implies the exact modular machine frame,
even for a partial loan and for high canonical allocations. -/
theorem word_loan_disjoint {shared : Shared} {owner loanId : Nat}
    {ticket : Ownership.Ticket} {address : Word} {loan : Borrowing.Loan}
    (valid : Borrowing.WellFormed shared)
    (word : Mutex.WordValid shared owner ticket address)
    (live : shared.loans loanId = some loan)
    (different : ticket.identifier ≠ loan.ticket.identifier) :
    DWordDisjoint address loan.region.base loan.region.length := by
  obtain ⟨allocation, found, _, _, fits, _⟩ := word
  obtain ⟨borrowed, foundBorrowed, _, _, subregion, regionValid, _⟩ := (valid.2 _ _ live).2
  have separate := valid.1.2 _ _ _ _ found foundBorrowed different
  have restricted : Ownership.Disjoint allocation.region loan.region := by
    rcases separate with before | after
    · exact Or.inl (Nat.le_trans before subregion.1)
    · exact Or.inr (Nat.le_trans subregion.2 after)
  have allocationValid := (valid.1.1 _ _ found).2.1
  have bounds : allocation.region.base.toNat ≤ address.toNat ∧
      address.toNat + 4 ≤ allocation.region.base.toNat + allocation.region.length :=
    of_decide_eq_true fits
  have limit := (of_decide_eq_true allocationValid).2.1
  have noWrap : address.toNat + 3 < 2^64 := by omega
  intro offset bound
  have inside : loan.region.Contains (loan.region.base + BitVec.ofNat 64 offset) :=
    Ownership.addresses_inside loan.region regionValid _
      (List.mem_map.mpr ⟨offset, List.mem_range.mpr bound, rfl⟩)
  by_cases outside : 4 ≤ ((loan.region.base + BitVec.ofNat 64 offset) - address).toNat
  · exact outside
  · exact False.elim (Ownership.disjoint_outside restricted inside
      (Ownership.containsWord_inside allocation address _ fits
        ((AddressSpace.word_contains_iff address _ noWrap).mpr (by omega))))

theorem word_hasLoan_disjoint {shared : Shared} {owner worker loanId : Nat}
    {ticket : Ownership.Ticket} {address : Word} {region : AddressSpace.Region}
    (valid : Borrowing.WellFormed shared)
    (word : Mutex.WordValid shared owner ticket address)
    (held : Threads.HasLoan shared worker loanId region)
    (unborrowed : ∀ identifier loan, shared.loans identifier = some loan →
      loan.ticket.identifier ≠ ticket.identifier) :
    DWordDisjoint address region.base region.length := by
  obtain ⟨loan, live, _, sameRegion⟩ := held
  subst region
  exact word_loan_disjoint valid word live (unborrowed _ _ live).symm

/-- Present authority and actual cells, without decoding or execution premises.
The full allocation exclusion is the existing Borrowing gate's contract. -/
structure Contract (call : Call) (shared : Shared) : Prop where
  wellFormed : Borrowing.WellFormed shared
  codeLoan : Threads.HasLoan shared call.worker call.codeLoan ⟨call.code, call.bytes.length⟩
  stackLoan : Threads.HasLoan shared call.worker call.stackLoan ⟨call.stack, 8⟩
  code : CodeAt (AddressSpace.toMemory shared.resources.space) call.code call.bytes
  stack : readWord (AddressSpace.toMemory shared.resources.space) call.stack = .ok call.returnAddress
  word : Mutex.WordValid shared (Threads.principal call.worker) call.ticket call.targetPointer
  unborrowed : ∀ identifier loan, shared.loans identifier = some loan →
    loan.ticket.identifier ≠ call.ticket.identifier
  codeDisjoint : DWordDisjoint call.targetPointer call.code call.bytes.length
  stackDisjoint : DWordDisjoint call.targetPointer call.stack 8
  returnCanonical : canonical call.returnAddress = true
  stackBound : call.stack.toNat + 8 < 2^64
  postStackCanonical : canonical (call.stack + 8) = true

structure Current (call : Call) (shared : Shared) (machine : State) : Prop where
  contract : Contract call shared
  coupled : machine.memory = AddressSpace.toMemory shared.resources.space

/-- Exact current RAM and decoded instruction advance after an ordinary store. -/
def storeAfterLength (before : State) (evolved : Shared) (length : Nat) : State :=
  { before with
    memory := AddressSpace.toMemory evolved.resources.space
    rip := before.rip + BitVec.ofNat 64 length }

/-- The two-byte legacy ordinary-store convenience state. -/
def storeAfter (before : State) (evolved : Shared) : State :=
  { before with memory := AddressSpace.toMemory evolved.resources.space, rip := before.rip + 2 }

/-- Resource effect for a registration-owned policy. Actual observation success
is proved separately; targetPointer is fixed by the immutable task input. -/
inductive WordEffect (owner : Nat) (ticket : Ownership.Ticket) (targetPointer : Word) :
    Shared → State → SeqInstruction → Observation → Shared → Prop where
  | readOnly {shared before instruction observation}
      (allowed : CFG.readOnly instruction = true) :
      WordEffect owner ticket targetPointer shared before instruction observation shared
  | store {shared evolved before instruction observation value}
      (intent : instruction.storeIntent before = some (targetPointer, value))
      (success : Borrowing.mutate shared (.store owner ticket targetPointer value) = .ok (evolved, none)) :
      WordEffect owner ticket targetPointer shared before instruction observation evolved

/-- Current authority derives OS gate success for arbitrary mathematical data. -/
theorem current_store_enabled {call : Call} {shared : Shared} {machine : State}
    (current : Current call shared machine) (value : BitVec 32) :
    ∃ evolved, Borrowing.mutate shared
      (.store (Threads.principal call.worker) call.ticket call.targetPointer value) = .ok (evolved, none) :=
  Mutex.store_admitted _ _ _ _ _ current.contract.word current.contract.unborrowed

/-- The checked OS store derives the actual sequential transition, with complete
RAM coupling. Successful machine execution is not a premise. -/
theorem actual_store_bridge {shared evolved : Shared} {before : State}
    {instruction : SeqInstruction} {owner : Nat} {ticket : Ownership.Ticket}
    {address : Word} {value : BitVec 32}
    (coupled : before.memory = AddressSpace.toMemory shared.resources.space)
    (decoded : Sequential.decodeAt before = .ok instruction)
    (intent : instruction.storeIntent before = some (address, value))
    (success : Borrowing.mutate shared (.store owner ticket address value) = .ok (evolved, none))
    (af : Bool) :
    step af before = .ok ⟨.next (storeAfterLength before evolved instruction.length), []⟩ ∧
      Mutex.StoreEffect shared evolved address value := by
  have effect := Mutex.store_effect success
  have machine : storeDWord before.memory address value =
      .ok (AddressSpace.toMemory evolved.resources.space) := by
    rw [coupled]
    exact effect.machine
  refine ⟨?_, effect⟩
  rw [step_eq_execute af decoded, execute_storeIntent af intent, machine]
  rfl

/-- Every live loan and its values survive one checked store. Allocation
metadata, including all owner/epoch tickets, is retained by StoreEffect. -/
theorem contract_store {call : Call} {shared evolved : Shared} {value : BitVec 32}
    (contract : Contract call shared)
    (success : Borrowing.mutate shared
      (.store (Threads.principal call.worker) call.ticket call.targetPointer value) = .ok (evolved, none)) :
    Contract call evolved ∧
      (∀ identifier loan, shared.loans identifier = some loan →
        ∀ query, loan.region.Contains query →
          evolved.resources.space.cells query = shared.resources.space.cells query) := by
  have effect := Mutex.store_effect success
  have history : Borrowing.History shared evolved := .next (.mutate success) .refl
  obtain ⟨codeLoan, codeCells⟩ := contract.codeLoan.frame contract.wellFormed history
    (congrFun effect.loans call.codeLoan)
  obtain ⟨stackLoan, stackCells⟩ := contract.stackLoan.frame contract.wellFormed history
    (congrFun effect.loans call.stackLoan)
  refine ⟨?_, ?_⟩
  · exact ⟨history.wellFormed contract.wellFormed, codeLoan, stackLoan,
      AddressSpace.agrees_code _ _ _ _ codeCells contract.code,
      (readWord_congr _ _ _ (AddressSpace.agrees_read _ _ _ _ stackCells)).trans contract.stack,
      effect.wordValid contract.word,
      fun identifier loan live => contract.unborrowed identifier loan (by rwa [← effect.loans]),
      contract.codeDisjoint, contract.stackDisjoint, contract.returnCanonical,
      contract.stackBound, contract.postStackCanonical⟩
  · intro identifier loan live query inside
    have below := (contract.wellFormed.2 identifier loan live).1
    exact (history.loan_stable contract.wellFormed identifier below loan
      ((congrFun effect.loans identifier).trans live)).2 query inside

/-- A concrete evolved OS state belongs to this actual checked machine step.
The effect contains exact four-byte readback, complete outside frame, all cell
permissions, allocations/frontier and loans/nextLoan equalities. -/
theorem current_store_step {call : Call} {shared : Shared} {before : State}
    {instruction : SeqInstruction} {value : BitVec 32}
    (current : Current call shared before)
    (decoded : Sequential.decodeAt before = .ok instruction)
    (intent : instruction.storeIntent before = some (call.targetPointer, value)) (af : Bool) :
    ∃ evolved,
      Borrowing.mutate shared (.store (Threads.principal call.worker) call.ticket call.targetPointer value) =
        .ok (evolved, none) ∧
      step af before = .ok ⟨.next (storeAfterLength before evolved instruction.length), []⟩ ∧
      Current call evolved (storeAfterLength before evolved instruction.length) ∧
      Mutex.StoreEffect shared evolved call.targetPointer value ∧
      (∀ identifier loan, shared.loans identifier = some loan →
        ∀ query, loan.region.Contains query →
          evolved.resources.space.cells query = shared.resources.space.cells query) := by
  obtain ⟨evolved, stored⟩ := current_store_enabled current value
  obtain ⟨actual, effect⟩ := actual_store_bridge current.coupled decoded intent stored af
  obtain ⟨contract, loans⟩ := contract_store current.contract stored
  exact ⟨evolved, stored, actual, ⟨contract, rfl⟩, effect, loans⟩

/-- An actual full-width register copy retains the current OS world and its
complete RAM coupling. Original code/stack loans survive even if RSP changes;
an actual RET still requires its separate caller-slot binding. -/
theorem current_movReg64_step {call : Call} {shared : Shared} {before : State}
    {destination source : Register}
    (current : Current call shared before)
    (decoded : Sequential.decodeAt before = .ok (.movReg64 destination source)) (af : Bool) :
    ∃ after, step af before = .ok ⟨.next after, []⟩ ∧
      Current call shared after ∧ after.registers destination = before.registers source ∧
      (∀ register, register ≠ destination → after.registers register = before.registers register) ∧
      after.memory = before.memory ∧ after.flags = before.flags ∧ after.rip = before.rip + 3 := by
  obtain ⟨after, executed, assigned, other, memory, flags, pc⟩ :=
    execute_movReg64_context before destination source af
  refine ⟨after, ?_, ⟨current.contract, memory.trans current.coupled⟩,
    assigned, other, memory, flags, pc⟩
  rw [step_eq_execute af decoded]
  exact executed

/-- A register exchange retains the same current OS world, including the full
RAM coupling and the original caller-slot loan. Both assigned values come from
the pre-state, even when the operands alias. Exchanging RSP does not establish
the stack binding required by a later RET. -/
theorem current_xchgReg64_step {call : Call} {shared : Shared} {before : State}
    {left right : Register}
    (current : Current call shared before)
    (decoded : Sequential.decodeAt before = .ok (.xchgReg64 left right)) (af : Bool) :
    ∃ after, step af before = .ok ⟨.next after, []⟩ ∧
      Current call shared after ∧ after.registers left = before.registers right ∧
      after.registers right = before.registers left ∧
      (∀ register, register ≠ left → register ≠ right →
        after.registers register = before.registers register) ∧
      after.memory = before.memory ∧ after.flags = before.flags ∧ after.rip = before.rip + 3 := by
  obtain ⟨after, executed, leftValue, rightValue, other, memory, flags, pc⟩ :=
    execute_xchgReg64_context before left right af
  refine ⟨after, ?_, ⟨current.contract, memory.trans current.coupled⟩,
    leftValue, rightValue, other, memory, flags, pc⟩
  rw [step_eq_execute af decoded]
  exact executed

/-- The compact RAX exchange has the same resource contract as the ModRM
register exchange and advances by its actual two-byte encoding. -/
theorem current_xchgRax64_step {call : Call} {shared : Shared} {before : State}
    {other : Register}
    (current : Current call shared before)
    (decoded : Sequential.decodeAt before = .ok (.xchgRax64 other)) (af : Bool) :
    ∃ after, step af before = .ok ⟨.next after, []⟩ ∧
      Current call shared after ∧ after.registers .rax = before.registers other ∧
      after.registers other = before.registers .rax ∧
      (∀ register, register ≠ .rax → register ≠ other →
        after.registers register = before.registers register) ∧
      after.memory = before.memory ∧ after.flags = before.flags ∧ after.rip = before.rip + 2 := by
  obtain ⟨after, executed, raxValue, otherValue, untouched, memory, flags, pc⟩ :=
    execute_xchgRax64_context before other af
  refine ⟨after, ?_, ⟨current.contract, memory.trans current.coupled⟩,
    raxValue, otherValue, untouched, memory, flags, pc⟩
  rw [step_eq_execute af decoded]
  exact executed

/-- Current owner authorization and the complete-word permissions derive an
actual ordinary load at the fixed call target. The effective address is read
from the full PRE-state, even when the destination aliases an address register.
No target loan is created. The retained caller slot is independent of machine
RSP; a later RET still requires its own explicit stack binding. -/
theorem current_load_step {call : Call} {shared : Shared} {before : State}
    {destination : Register} {address : Address}
    (current : Current call shared before)
    (decoded : Sequential.decodeAt before = .ok (.loadMem32 destination address))
    (effective : address.eval before = call.targetPointer) (af : Bool) :
    ∃ (value : BitVec 32) (after : State),
      step af before = .ok ⟨.next after, [⟨.data, call.targetPointer, 4⟩]⟩ ∧
      after.registers destination = value.setWidth 64 ∧
      loadDWord before.memory call.targetPointer = .ok value ∧
      (∃ allocation,
        Ownership.authorize shared.resources (Threads.principal call.worker) call.ticket = .ok allocation ∧
        Ownership.containsWord allocation call.targetPointer = true) ∧
      OperandReadSucceeds before ⟨.data, call.targetPointer, 4⟩ ∧
      Current call shared after ∧
      (∀ register, register ≠ destination → after.registers register = before.registers register) ∧
      after.memory = before.memory ∧ after.flags = before.flags ∧
      after.rip = before.rip + BitVec.ofNat 64 (Sequential.Instruction.loadMem32 destination address).length := by
  obtain ⟨allocation, authorized, fits⟩ := current.contract.word.authorize
  obtain ⟨value, observed⟩ := current.contract.word.load_exists
  have loaded : loadDWord before.memory call.targetPointer = .ok value := by
    rw [current.coupled]
    exact observed
  let after : State := { before.writeRegister destination (value.setWidth 64) with
    rip := before.rip + BitVec.ofNat 64 (Sequential.Instruction.loadMem32 destination address).length }
  refine ⟨value, after, ?_, ?_, loaded, ⟨allocation, authorized, fits⟩,
    ⟨rfl, value, loaded⟩, ⟨current.contract, current.coupled⟩, ?_, rfl, rfl, rfl⟩
  · rw [step_eq_execute af decoded]
    simp only [execute_loadMem32, effective, loaded, ok_bind, pure_ok, after]
  · simp [after, State.writeRegister]
  · intro register different
    simp [after, State.writeRegister, different]

/-- Current authority follows actual readonly continuation or return steps. -/
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
  · exact ⟨after, Or.inl next, current.contract,
      (CFG.execute_next_memory allowed executed next).trans current.coupled⟩
  · exact ⟨after, Or.inr returned, current.contract,
      (CFG.execute_returned_memory allowed executed returned).trans current.coupled⟩

theorem wordEffect_history {owner : Nat} {ticket : Ownership.Ticket} {targetPointer : Word}
    {shared evolved : Shared} {before : State} {instruction : SeqInstruction} {observation : Observation}
    (effect : WordEffect owner ticket targetPointer shared before instruction observation evolved) :
    Borrowing.History shared evolved := by
  cases effect with
  | readOnly _ => exact .refl
  | store _ success => exact .next (.mutate success) .refl


end EDSL.OS.WordResources
