/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Mutex.History

namespace EDSL.OS.Mutex
open X86 AddressSpace

/-- Exact three-instruction compiler routine and its complete projected final
state. Guard/invariant checks belong to the protocol's admission contract;
this predicate does not claim that the XCHG routine executes those checks. -/
def ExchangeExecution (before after : Borrowing.State) (event : AtomicEvent)
    (initial : X86.State) (target : Word) : Prop :=
  let entry := { initial with memory := toMemory before.resources.space }
  let final := AtomicExchange.finalWithSpace entry after.resources.space event.before target
  AtomicExecutes entry final 3 [event] ∧ Executes entry final 3 ∧ ¬Diverges entry ∧
    ∀ other count, Executes entry other count → other = final ∧ count = 3

theorem tryAcquire_exchange32 (state : State) (actor : Nat) (result : Attempt) (record : Registered)
    (initial : X86.State) (target : Word) (success : tryAcquire state actor = .ok result)
    (live : state.mutex = some record) (operand : initial.registers .rdi = record.config.lockAddress)
    (value : (initial.registers .rsi).setWidth 32 = 1)
    (code : CodeAt (toMemory state.shared.resources.space) initial.rip Examples.Compiler.Exchange.bytes)
    (codeDisjoint : DWordDisjoint (initial.registers .rdi) initial.rip Examples.Compiler.Exchange.bytes.length)
    (stackDisjoint : DWordDisjoint (initial.registers .rdi) (initial.registers .rsp) 8)
    (stack : readWord (toMemory state.shared.resources.space) (initial.registers .rsp) = .ok target)
    (canonical : X86.canonical target = true) :
    ExchangeExecution state.shared result.state.shared result.event initial target := by
  obtain ⟨actual, exchanged, found, exchange, branches⟩ := tryAcquire_ok _ _ _ success
  have sameRecord := Option.some.inj (found.symm.trans live)
  subst actual
  have call : AtomicExchange.exchangeWord state.shared record.config.owner record.config.lockTicket
      (initial.registers .rdi) ((initial.registers .rsi).setWidth 32) = .ok exchanged := by
    simpa only [operand, value, BitVec.ofNat_eq_ofNat] using exchange
  have execution := AtomicExchange.exchange32_updates_space _ _ _ _ initial target call code codeDisjoint stackDisjoint stack canonical
  rcases branches with ⟨_, same⟩ | ⟨_, same⟩ <;> rw [same]
  all_goals
    simpa only [ExchangeExecution, Examples.Compiler.Exchange.event, operand, value] using execution

theorem release_exchange32 (state : State) (actor : Nat) (lease : Lease) (result : State × AtomicEvent)
    (record : Registered) (initial : X86.State) (target : Word) (success : release state actor lease = .ok result)
    (authorized : authorize state actor lease = .ok record) (operand : initial.registers .rdi = record.config.lockAddress)
    (value : (initial.registers .rsi).setWidth 32 = 0)
    (code : CodeAt (toMemory state.shared.resources.space) initial.rip Examples.Compiler.Exchange.bytes)
    (codeDisjoint : DWordDisjoint (initial.registers .rdi) initial.rip Examples.Compiler.Exchange.bytes.length)
    (stackDisjoint : DWordDisjoint (initial.registers .rdi) (initial.registers .rsp) 8)
    (stack : readWord (toMemory state.shared.resources.space) (initial.registers .rsp) = .ok target)
    (canonical : X86.canonical target = true) :
    ExchangeExecution state.shared result.1.shared result.2 initial target := by
  obtain ⟨actual, _, exchanged, selected, _, _, exchange, same⟩ := release_ok _ _ _ _ success
  have sameRecord := Except.ok.inj (selected.symm.trans authorized)
  subst actual
  have call : AtomicExchange.exchangeWord state.shared record.config.owner record.config.lockTicket
      (initial.registers .rdi) ((initial.registers .rsi).setWidth 32) = .ok exchanged := by
    simpa only [operand, value, BitVec.ofNat_eq_ofNat] using exchange
  have execution := AtomicExchange.exchange32_updates_space _ _ _ _ initial target call code codeDisjoint stackDisjoint stack canonical
  rw [same]
  simpa only [ExchangeExecution, Examples.Compiler.Exchange.event, operand, value] using execution

/-- The checked protected store projects to the exact two-instruction MOV/RET
routine; logical guard authority is not a hardware pointer tag. -/
theorem guardStore_store32 (state : State) (actor : Nat) (lease : Lease) (after : State)
    (record : Registered) (initial : X86.State) (target : Word)
    (success : guardStore state actor lease ((initial.registers .rsi).setWidth 32) = .ok after)
    (authorized : authorize state actor lease = .ok record)
    (operand : initial.registers .rdi = record.config.dataAddress)
    (code : CodeAt (toMemory state.shared.resources.space) initial.rip Examples.Compiler.MemoryOps.storeBytes)
    (codeDisjoint : DWordDisjoint (initial.registers .rdi) initial.rip Examples.Compiler.MemoryOps.storeBytes.length)
    (stackDisjoint : DWordDisjoint (initial.registers .rdi) (initial.registers .rsp) 8)
    (stack : readWord (toMemory state.shared.resources.space) (initial.registers .rsp) = .ok target)
    (canonical : X86.canonical target = true) :
    let entry := { initial with memory := toMemory state.shared.resources.space }
    Executes entry (storeFinalWithSpace entry after.shared.resources.space target) 2 ∧
      ¬Diverges entry ∧ ∀ other count, Executes entry other count →
        other = storeFinalWithSpace entry after.shared.resources.space target ∧ count = 2 := by
  obtain ⟨actual, result, selected, changed, same⟩ := guardStore_ok _ _ _ _ _ success
  have sameRecord := Except.ok.inj (selected.symm.trans authorized)
  subst actual
  obtain ⟨_, resources, mutation, sharedEq⟩ := Borrowing.mutate_ok _ _ _ changed
  cases stored : Ownership.storeWord state.shared.resources record.config.owner record.config.dataTicket
      record.config.dataAddress ((initial.registers .rsi).setWidth 32) with
  | error fault => simp [Ownership.Mutation.run, stored, Except.map] at mutation
  | ok world =>
    simp [Ownership.Mutation.run, stored, Except.map] at mutation
    subst resources
    have call : Ownership.storeWord state.shared.resources record.config.owner record.config.dataTicket
        (initial.registers .rdi) ((initial.registers .rsi).setWidth 32) = .ok world := by simpa only [operand] using stored
    rw [same, sharedEq]
    exact Ownership.owned_store32_correct _ _ _ _ initial target call code codeDisjoint stackDisjoint stack canonical

theorem guardLoad_load32 (state : State) (actor : Nat) (lease : Lease) (value : BitVec 32)
    (record : Registered) (initial : X86.State) (target : Word)
    (success : guardLoad state actor lease = .ok value) (authorized : authorize state actor lease = .ok record)
    (operand : initial.registers .rdi = record.config.dataAddress)
    (code : CodeAt (toMemory state.shared.resources.space) initial.rip Examples.Compiler.MemoryOps.loadBytes)
    (stack : readWord (toMemory state.shared.resources.space) (initial.registers .rsp) = .ok target)
    (canonical : X86.canonical target = true) :
    let entry := { initial with memory := toMemory state.shared.resources.space }
    Executes entry (Examples.Compiler.MemoryOps.loadFinal entry value target) 2 ∧
      ¬Diverges entry ∧ ∀ other count, Executes entry other count →
        other = Examples.Compiler.MemoryOps.loadFinal entry value target ∧ count = 2 := by
  cases read : loadDWord (toMemory state.shared.resources.space) record.config.dataAddress with
  | error fault => simp [guardLoad, authorized, read, Except.mapError] at success
  | ok actual =>
    simp [guardLoad, authorized, read, Except.mapError] at success
    subst actual
    exact Examples.Compiler.MemoryOps.load_correct _ _ _ code (by simpa only [operand] using read) stack canonical

end EDSL.OS.Mutex
