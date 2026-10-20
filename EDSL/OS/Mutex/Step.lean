/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Mutex.Machine

namespace EDSL.OS.Mutex
open X86 AddressSpace

/-- Complete projected result of one lock-word XCHG. All registers except RAX,
all flags, and the instruction's exact two-byte advancement are retained. -/
def afterExchange (initial : X86.State) (space : Space) (old : BitVec 32) : X86.State :=
  { initial.writeRegister .rax (old.setWidth 64) with memory := toMemory space, rip := initial.rip + 2 }

def afterLoad (initial : X86.State) (space : Space) (value : BitVec 32) : X86.State :=
  { initial.writeRegister .rax (value.setWidth 64) with memory := toMemory space, rip := initial.rip + 2 }

def afterStore (initial : X86.State) (space : Space) : X86.State :=
  { initial with memory := toMemory space, rip := initial.rip + 2 }

/-- Every successful checked attempt corresponds to the actual decoded XCHG
against current OS cells, including a busy attempt's real 1-to-1 exchange.
Logical admission and physical architecture conformance remain separate. -/
theorem tryAcquire_step (state : State) (actor : Nat) (result : Attempt)
    (record : Registered) (initial : X86.State)
    (success : tryAcquire state actor = .ok result)
    (live : state.mutex = some record)
    (memory : initial.memory = toMemory state.shared.resources.space)
    (operand : initial.registers .rdi = record.config.lockAddress)
    (replacement : (initial.registers .rax).setWidth 32 = 1)
    (decoded : decodeAt initial = .ok .exchangeEaxRdi) :
    X86.step initial = .ok (.atomic result.event
      (afterExchange initial result.state.shared.resources.space result.event.before)) := by
  obtain ⟨actual, exchanged, found, exchange, branches⟩ := tryAcquire_ok _ _ _ success
  have equal := Option.some.inj (found.symm.trans live)
  subst actual
  have transition := AtomicExchange.exchangeWord_sound _ _ _ _ _ _ exchange
  have exchangedMachine := X86.exchangeDWord_success _ record.config.lockAddress exchanged.2 1
    transition.1 transition.2.1 transition.2.2.1
  simp only [BitVec.ofNat_eq_ofNat] at exchangedMachine
  have actualStep : X86.step initial = .ok (.atomic ⟨record.config.lockAddress, exchanged.2, 1⟩
      (afterExchange initial exchanged.1.resources.space exchanged.2)) := by
    simp [X86.step, decoded, executeExchange, operand, replacement, memory, exchangedMachine,
      afterExchange, transition.2.2.2]
  rcases branches with ⟨_, same⟩ | ⟨_, same⟩ <;> rw [same] <;> exact actualStep

/-- Checked release's current-payload invariant is supplied by the successful
protocol operation; the instruction itself only performs its actual XCHG.
The complete resulting machine memory equals the released state's OS cells. -/
theorem release_step (state : State) (actor : Nat) (lease : Lease)
    (result : State × AtomicEvent) (record : Registered) (initial : X86.State)
    (success : release state actor lease = .ok result)
    (authorized : authorize state actor lease = .ok record)
    (memory : initial.memory = toMemory state.shared.resources.space)
    (operand : initial.registers .rdi = record.config.lockAddress)
    (replacement : (initial.registers .rax).setWidth 32 = 0)
    (decoded : decodeAt initial = .ok .exchangeEaxRdi) :
    X86.step initial = .ok (.atomic result.2
      (afterExchange initial result.1.shared.resources.space result.2.before)) := by
  obtain ⟨actual, _, exchanged, checked, _, _, exchange, same⟩ := release_ok _ _ _ _ success
  have equal := Except.ok.inj (checked.symm.trans authorized)
  subst actual
  have transition := AtomicExchange.exchangeWord_sound _ _ _ _ _ _ exchange
  have exchangedMachine := X86.exchangeDWord_success _ record.config.lockAddress exchanged.2 0
    transition.1 transition.2.1 transition.2.2.1
  simp only [BitVec.ofNat_eq_ofNat] at exchangedMachine
  rw [same]
  simp [X86.step, decoded, executeExchange, operand, replacement, memory, exchangedMachine,
    afterExchange, transition.2.2.2]

/-- A guard-authorized current payload observation is exactly one decoded
MOV EAX,[RSI], with unchanged shared memory and flags. -/
theorem guardLoad_step (state : State) (actor : Nat) (lease : Lease) (value : BitVec 32)
    (record : Registered) (initial : X86.State)
    (success : guardLoad state actor lease = .ok value)
    (authorized : authorize state actor lease = .ok record)
    (memory : initial.memory = toMemory state.shared.resources.space)
    (operand : initial.registers .rsi = record.config.dataAddress)
    (decoded : decodeAt initial = .ok .loadEaxRsi) :
    X86.step initial = .ok (.next (afterLoad initial state.shared.resources.space value)) := by
  have observed : loadDWord (toMemory state.shared.resources.space) record.config.dataAddress = .ok value := by
    cases read : loadDWord (toMemory state.shared.resources.space) record.config.dataAddress with
    | error fault => simp [guardLoad, authorized, read, Except.mapError] at success
    | ok actual =>
      simp [guardLoad, authorized, read, Except.mapError] at success
      subst actual
      rfl
  simp [X86.step, decoded, executeLoadRsi, memory, operand, observed, afterLoad, X86.State.writeRegister]

/-- One actual MOV [RSI],EAX updates the complete projected memory to the
guarded store's resulting OS cells. No payload invariant is required while the
guard remains held; closing it is a separate release obligation. -/
theorem guardStore_step (state : State) (actor : Nat) (lease : Lease) (value : BitVec 32)
    (after : State) (record : Registered) (initial : X86.State)
    (success : guardStore state actor lease value = .ok after)
    (authorized : authorize state actor lease = .ok record)
    (memory : initial.memory = toMemory state.shared.resources.space)
    (operand : initial.registers .rsi = record.config.dataAddress)
    (replacement : (initial.registers .rax).setWidth 32 = value)
    (decoded : decodeAt initial = .ok .storeEaxRsi) :
    X86.step initial = .ok (.next (afterStore initial after.shared.resources.space)) := by
  obtain ⟨actual, changed, checked, stored, same⟩ := guardStore_ok _ _ _ _ _ success
  have equal := Except.ok.inj (checked.symm.trans authorized)
  subst actual
  have noTicket := store_none stored
  have storedNone : Borrowing.mutate state.shared
      (.store record.config.owner record.config.dataTicket record.config.dataAddress value) = .ok (changed.1, none) := by
    rw [← noTicket]
    exact stored
  have machine := (store_effect storedNone).machine
  rw [same]
  simp [X86.step, decoded, executeStoreRsi, memory, operand, replacement, machine, afterStore]

end EDSL.OS.Mutex
