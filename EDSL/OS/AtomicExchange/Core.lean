/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Borrowing.Read.Core
import EDSL.X86.AtomicMemory

namespace EDSL.OS.AtomicExchange
open X86 AddressSpace

inductive Fault where
  | authority (fault : Borrowing.Fault)
  | machine (fault : X86.Error)
  deriving DecidableEq, Repr

@[simp] theorem throw_error (fault : Fault) : (throw fault : Except Fault α) = .error fault := rfl

/-- A single checked exchange of the current shared cells. The ordinary store
is used only as a pure authority/loan gate and OS-cell updater; it is not a
separate exposed execution step. The X86 exchange checks the supported atomic
operand and supplies the old value from the original current memory.

A live read loan freezes the whole allocation. This operation does not create
shared atomic authority, authenticate principals, or extend the read-only
managed-worker instruction profile. -/
def exchangeWord (state : Borrowing.State) (owner : Nat) (ticket : Ownership.Ticket)
    (address : Word) (value : BitVec 32) : Except Fault (Borrowing.State × BitVec 32) := do
  let guarded ← (Borrowing.mutate state (.store owner ticket address value)).mapError Fault.authority
  let exchanged ← (X86.exchangeDWord (toMemory state.resources.space) address value).mapError Fault.machine
  return (guarded.1, exchanged.2)

theorem exchangeWord_ok (state : Borrowing.State) (owner : Nat) (ticket : Ownership.Ticket)
    (address : Word) (value : BitVec 32) (result : Borrowing.State × BitVec 32)
    (success : exchangeWord state owner ticket address value = .ok result) :
    ∃ guarded exchanged,
      Borrowing.mutate state (.store owner ticket address value) = .ok guarded ∧
      X86.exchangeDWord (toMemory state.resources.space) address value = .ok exchanged ∧
      result = (guarded.1, exchanged.2) := by
  cases gate : Borrowing.mutate state (.store owner ticket address value) with
  | error fault => simp [exchangeWord, gate, Except.mapError] at success
  | ok guarded =>
    cases machine : X86.exchangeDWord (toMemory state.resources.space) address value with
    | error fault => simp [exchangeWord, gate, machine, Except.mapError] at success
    | ok exchanged =>
      simp [exchangeWord, gate, machine, Except.mapError] at success
      exact ⟨guarded, exchanged, rfl, rfl, success.symm⟩

/-- Every accepted exchange is an admitted borrowing mutation, so the existing
resource invariant and surviving read-loan contracts continue to apply. -/
theorem exchangeWord_guarded (state : Borrowing.State) (owner : Nat) (ticket : Ownership.Ticket)
    (address : Word) (value : BitVec 32) (result : Borrowing.State × BitVec 32)
    (success : exchangeWord state owner ticket address value = .ok result) :
    Borrowing.mutate state (.store owner ticket address value) = .ok (result.1, none) := by
  obtain ⟨guarded, exchanged, gate, _, same⟩ := exchangeWord_ok _ _ _ _ _ _ success
  obtain ⟨_, resources, changed, resultEq⟩ := Borrowing.mutate_ok _ _ _ gate
  cases stored : Ownership.storeWord state.resources owner ticket address value with
  | error fault => simp [Ownership.Mutation.run, stored, Except.map] at changed
  | ok world =>
    simp [Ownership.Mutation.run, stored, Except.map] at changed
    subst resources
    rw [same, resultEq]
    simpa only [resultEq] using gate

/-- The logical store and the machine RMW commute to the same final memory.
The returned old word is bound to the actual pre-exchange memory, and there is
one abstract transition with no observable load/store intermediate state. -/
theorem exchangeWord_sound (state : Borrowing.State) (owner : Nat) (ticket : Ownership.Ticket)
    (address : Word) (value : BitVec 32) (result : Borrowing.State × BitVec 32)
    (success : exchangeWord state owner ticket address value = .ok result) :
    ExchangeTransition (toMemory state.resources.space) ⟨address, result.2, value⟩
      (toMemory result.1.resources.space) := by
  obtain ⟨guarded, exchanged, gate, machine, same⟩ := exchangeWord_ok _ _ _ _ _ _ success
  obtain ⟨_, resources, changed, resultEq⟩ := Borrowing.mutate_ok _ _ _ gate
  cases stored : Ownership.storeWord state.resources owner ticket address value with
  | error fault => simp [Ownership.Mutation.run, stored, Except.map] at changed
  | ok world =>
    simp [Ownership.Mutation.run, stored, Except.map] at changed
    subst resources
    obtain ⟨allocation, space, _, _, osStore, worldEq⟩ := Ownership.storeWord_ok _ _ _ _ _ _ stored
    obtain ⟨spaceEq, allowed⟩ := AddressSpace.storeWord_ok _ _ _ _ osStore
    have transition := X86.exchangeDWord_ok _ _ _ _ machine
    rw [same, resultEq]
    change ExchangeTransition (toMemory state.resources.space) ⟨address, exchanged.2, value⟩
      (toMemory world.space)
    rw [worldEq, spaceEq, writeWord_projects _ _ _ allowed]
    exact ⟨transition.1, transition.2.1, transition.2.2.1, rfl⟩

theorem exchangeWord_success (state : Borrowing.State) (owner : Nat) (ticket : Ownership.Ticket)
    (address : Word) (old value : BitVec 32) (after : Borrowing.State)
    (gate : Borrowing.mutate state (.store owner ticket address value) = .ok (after, none))
    (supported : atomicAddressable address = true)
    (allowed : canStoreDWord (toMemory state.resources.space) address = true)
    (read : loadDWord (toMemory state.resources.space) address = .ok old) :
    exchangeWord state owner ticket address value = .ok (after, old) := by
  have machine := X86.exchangeDWord_success _ address old value supported allowed read
  simp [exchangeWord, gate, machine, Except.mapError]

theorem exchangeWord_wellFormed (state : Borrowing.State) (owner : Nat) (ticket : Ownership.Ticket)
    (address : Word) (value : BitVec 32) (result : Borrowing.State × BitVec 32)
    (valid : Borrowing.WellFormed state)
    (success : exchangeWord state owner ticket address value = .ok result) :
    Borrowing.WellFormed result.1 :=
  Borrowing.mutate_wellFormed _ _ _ valid (exchangeWord_guarded _ _ _ _ _ _ success)

/-- Rejection covers every live loan under the explicit registry invariant,
including a loan on a disjoint subregion of the same allocation. -/
theorem exchangeWord_borrowed (state : Borrowing.State) (owner : Nat) (ticket : Ownership.Ticket)
    (address : Word) (value : BitVec 32) (identifier : Nat) (loan : Borrowing.Loan)
    (valid : Borrowing.WellFormed state) (live : state.loans identifier = some loan)
    (sameAllocation : loan.ticket.identifier = ticket.identifier) :
    exchangeWord state owner ticket address value = .error (.authority .borrowed) := by
  have blocked : Borrowing.allowed state (.store owner ticket address value) = false := by
    cases checked : Borrowing.allowed state (.store owner ticket address value) with
    | false => rfl
    | true =>
      have different := Borrowing.allowed_sound state (.store owner ticket address value)
        valid checked identifier loan live
      simp [Ownership.Mutation.target, sameAllocation] at different
  simp [exchangeWord, Borrowing.mutate, blocked, Except.mapError]

/-- The returned machine state retains the resource-managed OS cells. -/
def finalWithSpace (initial : X86.State) (space : Space) (old : BitVec 32)
    (returnAddress : Word) : X86.State :=
  { initial with
    registers := fun register => if register = .rsp then initial.registers .rsp + 8
      else if register = .rax then old.setWidth 64 else initial.registers register
    rip := returnAddress
    memory := toMemory space }

/-- Principal and current ticket are logical authority labels. They are not an
authenticated thread identity or a claim of shared mutable worker support. -/
structure Event where
  owner : Nat
  ticket : Ownership.Ticket
  exchange : AtomicEvent
  deriving DecidableEq, Repr

inductive Step : Borrowing.State → Event → Borrowing.State → Prop where
  | exchange {before after owner ticket address value old}
      (success : exchangeWord before owner ticket address value = .ok (after, old)) :
      Step before ⟨owner, ticket, ⟨address, old, value⟩⟩ after

theorem Step.sound {before after : Borrowing.State} {event : Event}
    (step : Step before event after) :
    ExchangeTransition (toMemory before.resources.space) event.exchange (toMemory after.resources.space) := by
  cases step with
  | exchange success => exact exchangeWord_sound _ _ _ _ _ _ success

theorem Step.guarded {before after : Borrowing.State} {event : Event}
    (step : Step before event after) : Borrowing.Step before after := by
  cases step with
  | exchange success => exact .mutate (exchangeWord_guarded _ _ _ _ _ _ success)

/-- Arbitrary finite schedules of exchanges of one cell. Admission reads the
current state at each step, so no spawn-time or caller-supplied old word is used.
Resource transfers and general machine interleavings are outside this relation. -/
inductive History (address : Word) : Borrowing.State → Borrowing.State → List Event → Prop where
  | refl {state} : History address state state []
  | next {before middle after event events}
      (atCell : event.exchange.address = address)
      (first : Step before event middle)
      (tail : History address middle after events) : History address before after (event :: events)

/-- Independently stated value-flow contract: every old result equals the
previous exchange's new value, starting from the initially observed word. -/
inductive Chain : BitVec 32 → List Event → BitVec 32 → Prop where
  | nil {value} : Chain value [] value
  | cons {old event events final} (observed : event.exchange.before = old)
      (tail : Chain event.exchange.after events final) : Chain old (event :: events) final

theorem History.guarded {address : Word} {before after : Borrowing.State} {events : List Event}
    (history : History address before after events) : Borrowing.History before after := by
  induction history with
  | refl => exact .refl
  | next _ first _ induction => exact .next first.guarded induction

theorem History.wellFormed {address : Word} {before after : Borrowing.State} {events : List Event}
    (history : History address before after events) (valid : Borrowing.WellFormed before) :
    Borrowing.WellFormed after := history.guarded.wellFormed valid

theorem History.chain {address : Word} {before after : Borrowing.State} {events : List Event}
    (history : History address before after events) (old : BitVec 32)
    (observed : loadDWord (toMemory before.resources.space) address = .ok old) :
    ∃ final, loadDWord (toMemory after.resources.space) address = .ok final ∧ Chain old events final := by
  induction history generalizing old with
  | refl => exact ⟨old, observed, .nil⟩
  | @next before middle after event events atCell first tail induction =>
    have transition := first.sound
    have read := transition.2.2.1
    rw [atCell] at read
    have oldEq := Except.ok.inj (read.symm.trans observed)
    have written := transition.readback
    rw [atCell] at written
    obtain ⟨final, readFinal, chain⟩ := induction event.exchange.after written
    exact ⟨final, readFinal, .cons oldEq chain⟩

/-- Surviving read authority retains bytes and permissions across all exchanges,
by composing with the existing borrowing history contract. -/
theorem History.loan_stable {address : Word} {before after : Borrowing.State} {events : List Event}
    (history : History address before after events) (valid : Borrowing.WellFormed before)
    (identifier : Nat) (below : identifier < before.nextLoan) (loan : Borrowing.Loan)
    (live : after.loans identifier = some loan) :
    before.loans identifier = some loan ∧
    ∀ query, loan.region.Contains query → after.resources.space.cells query = before.resources.space.cells query :=
  history.guarded.loan_stable valid identifier below loan live

end EDSL.OS.AtomicExchange
