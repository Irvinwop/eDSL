/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Atomics.History
import EDSL.OS.AtomicExchange

namespace EDSL.OS.Atomics
open X86 AddressSpace

theorem exchange_sound (state : State) (actor identifier : Nat) (value : BitVec 32)
    (result : State × BitVec 32) (success : exchange state actor identifier value = .ok result) :
    ∃ handle, authorize state actor identifier = .ok handle ∧
      ExchangeTransition (toMemory state.shared.resources.space) ⟨handle.address, result.2, value⟩
        (toMemory result.1.shared.resources.space) := by
  obtain ⟨handle, shared, authorized, exchanged, same⟩ := exchange_ok _ _ _ _ _ success
  subst result
  exact ⟨handle, authorized, AtomicExchange.exchangeWord_sound _ _ _ _ _ _ exchanged⟩

def afterExchange (initial : X86.State) (space : Space) (old : BitVec 32) : X86.State :=
  { initial.writeRegister .rax (old.setWidth 64) with memory := toMemory space, rip := initial.rip + 2 }

/-- The checked shared-handle exchange and actual decoded XCHG step produce
the same event and projected final memory. The old word is current at dispatch,
not retained from handle issuance. Physical conformance stays external. -/
theorem exchange_step (state : State) (actor identifier : Nat) (value : BitVec 32)
    (result : State × BitVec 32) (handle : Handle) (initial : X86.State)
    (success : exchange state actor identifier value = .ok result)
    (authorized : authorize state actor identifier = .ok handle)
    (memory : initial.memory = toMemory state.shared.resources.space)
    (operand : initial.registers .rdi = handle.address)
    (replacement : (initial.registers .rax).setWidth 32 = value)
    (decoded : decodeAt initial = .ok .exchangeEaxRdi) :
    X86.step initial = .ok (.atomic ⟨handle.address, result.2, value⟩
      (afterExchange initial result.1.shared.resources.space result.2)) := by
  obtain ⟨selected, observed, transition⟩ := exchange_sound _ _ _ _ _ success
  have equal := Except.ok.inj (authorized.symm.trans observed)
  subst selected
  have exchanged := X86.exchangeDWord_success _ handle.address result.2 value
    transition.1 transition.2.1 transition.2.2.1
  simp [X86.step, decoded, executeExchange, operand, replacement, memory, exchanged,
    afterExchange, transition.2.2.2]

/-- The exact three-instruction routine implements the shared-handle operation
and retains its singleton event, termination and unique result/count. -/
theorem exchange32_updates_space (state : State) (actor identifier : Nat)
    (result : State × BitVec 32) (handle : Handle) (initial : X86.State) (returnAddress : Word)
    (success : exchange state actor identifier ((initial.registers .rsi).setWidth 32) = .ok result)
    (authorized : authorize state actor identifier = .ok handle)
    (operand : initial.registers .rdi = handle.address)
    (code : CodeAt (toMemory state.shared.resources.space) initial.rip Examples.Compiler.Exchange.bytes)
    (codeDisjoint : DWordDisjoint (initial.registers .rdi) initial.rip Examples.Compiler.Exchange.bytes.length)
    (stackDisjoint : DWordDisjoint (initial.registers .rdi) (initial.registers .rsp) 8)
    (stack : readWord (toMemory state.shared.resources.space) (initial.registers .rsp) = .ok returnAddress)
    (returnValid : canonical returnAddress = true) :
    let entry := { initial with memory := toMemory state.shared.resources.space }
    let final := AtomicExchange.finalWithSpace entry result.1.shared.resources.space result.2 returnAddress
    AtomicExecutes entry final 3 [Examples.Compiler.Exchange.event entry result.2] ∧
    Executes entry final 3 ∧ ¬ Diverges entry ∧
    ∀ other count, Executes entry other count → other = final ∧ count = 3 := by
  obtain ⟨selected, shared, observed, exchanged, same⟩ := exchange_ok _ _ _ _ _ success
  have equal := Except.ok.inj (authorized.symm.trans observed)
  subst selected
  subst result
  rw [← operand] at exchanged
  exact AtomicExchange.exchange32_updates_space _ _ _ _ _ _ exchanged code codeDisjoint stackDisjoint stack returnValid

theorem load_exists_of_canStore (memory : Memory) (address : Word)
    (allowed : canStoreDWord memory address = true) : ∃ value, loadDWord memory address = .ok value := by
  have valid := (Bool.and_eq_true_iff.mp allowed).1
  have mapped := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp allowed).2).2
  simp only [Bool.and_eq_true] at mapped
  rcases mapped with ⟨⟨⟨m0, m1⟩, m2⟩, m3⟩
  change (memory.read (address + 1)).isSome = true at m1
  change (memory.read (address + 2)).isSome = true at m2
  change (memory.read (address + 3)).isSome = true at m3
  cases b0 : memory.read address with
  | none => rw [b0] at m0; cases m0
  | some v0 =>
    cases b1 : memory.read (address + 1) with
    | none => rw [b1] at m1; cases m1
    | some v1 =>
      cases b2 : memory.read (address + 2) with
      | none => rw [b2] at m2; cases m2
      | some v2 =>
        cases b3 : memory.read (address + 3) with
        | none => rw [b3] at m3; cases m3
        | some v3 =>
          simp only [dwordAddressable, Bool.and_eq_true, decide_eq_true_eq] at valid
          obtain ⟨bound, ⟨⟨⟨c0, c1⟩, c2⟩, c3⟩⟩ := valid
          simp only [BitVec.ofNat_eq_ofNat] at b0 b1 b2 b3 c0 c1 c2 c3
          exact ⟨joinDWord v0 v1 v2 v3, by
            simp [loadDWord, readDataByte, show ¬ address.toNat + 3 ≥ 2^64 by omega,
              c0, c1, c2, c3, b0, b1, b2, b3]⟩

/-- Well-formed live authority always admits an exchange for every replacement
word. This supplies positive behavior, not a scheduling/progress assumption. -/
theorem exchange_enabled (state : State) (actor identifier : Nat) (handle : Handle)
    (value : BitVec 32) (valid : WellFormed state)
    (authorized : authorize state actor identifier = .ok handle) :
    ∃ result, exchange state actor identifier value = .ok result := by
  have live := (authorize_ok _ _ _ _ authorized).1
  obtain ⟨_, allocation, found, owns, epoch, fits, supported, writable⟩ := valid.handles _ _ live
  have owner : Ownership.authorize state.shared.resources handle.owner handle.ticket = .ok allocation := by
    simp [Ownership.authorize, found, epoch, owns]
  have unborrowed : Borrowing.allowed state.shared (.store handle.owner handle.ticket handle.address value) = true := by
    apply List.all_eq_true.mpr
    intro loanId _
    cases reader : state.shared.loans loanId with
    | none => rfl
    | some loan =>
      have different := valid.noReaders identifier handle live loanId loan reader
      change decide (some handle.ticket.identifier ≠ some loan.ticket.identifier) = true
      simpa only [decide_eq_true_eq, ne_eq, Option.some.injEq] using Ne.symm different
  let world := { state.shared.resources with space := writeWordCells state.shared.resources.space handle.address value }
  let shared := { state.shared with resources := world }
  have stored : Ownership.storeWord state.shared.resources handle.owner handle.ticket handle.address value = .ok world :=
    Ownership.storeWord_success _ _ _ _ _ _ owner fits writable
  have gate : Borrowing.mutate state.shared (.store handle.owner handle.ticket handle.address value) = .ok (shared, none) := by
    simp [Borrowing.mutate, unborrowed, Ownership.Mutation.run, stored, Except.map, Except.mapError, shared]
  obtain ⟨old, read⟩ := load_exists_of_canStore _ _ writable
  have exchanged := AtomicExchange.exchangeWord_success _ _ _ _ old value shared gate supported writable read
  exact ⟨({ state with shared := shared }, old), by simp [exchange, authorized, exchanged, Except.mapError]⟩

end EDSL.OS.Atomics
