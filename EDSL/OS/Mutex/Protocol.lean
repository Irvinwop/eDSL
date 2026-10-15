/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Mutex.Enabled

namespace EDSL.OS.Mutex
open X86 AddressSpace

theorem register_enabled (state : State) (config : Config) (absent : state.mutex = none)
    (separate : config.lockTicket.identifier ≠ config.dataTicket.identifier)
    (lock : WordValid state.shared config.owner config.lockTicket config.lockAddress)
    (data : WordValid state.shared config.owner config.dataTicket config.dataAddress)
    (atomic : atomicAddressable config.lockAddress = true) (readers : NoReaders state.shared config)
    (observed : loadDWord (toMemory state.shared.resources.space) config.lockAddress = .ok 0)
    (closed : Closed state.shared config) :
    register state config = .ok { state with mutex := some ⟨config, none⟩ } := by
  obtain ⟨lockAllocation, lockAuth, lockFits⟩ := lock.authorize
  obtain ⟨dataAllocation, dataAuth, dataFits⟩ := data.authorize
  have lockWritable := lock.writable
  have dataWritable := data.writable
  have lockLoans := unborrowed state.shared config.owner config.lockTicket config.lockAddress 0
    (fun identifier loan live => (readers identifier loan live).1)
  have dataLoans := unborrowed state.shared config.owner config.dataTicket config.dataAddress 0
    (fun identifier loan live => (readers identifier loan live).2)
  obtain ⟨value, dataRead, invariant⟩ := closed
  simp only [BitVec.ofNat_eq_ofNat] at observed lockLoans dataLoans
  simp [register, absent, separate, lockAuth, dataAuth, lockFits, dataFits,
    atomic, lockWritable, dataWritable, lockLoans, dataLoans, observed, dataRead, invariant, Except.mapError]

theorem guardStore_authorized (state : State) (actor : Nat) (lease : Lease) (value : BitVec 32)
    (after : State) (record : Registered) (authorized : authorize state actor lease = .ok record)
    (success : guardStore state actor lease value = .ok after) : authorize after actor lease = .ok record := by
  obtain ⟨_, _, _, _, same⟩ := guardStore_ok _ _ _ _ _ success
  rw [same]
  exact authorized

theorem guardStore_value (state : State) (actor : Nat) (lease : Lease) (value : BitVec 32)
    (after : State) (record : Registered) (authorized : authorize state actor lease = .ok record)
    (success : guardStore state actor lease value = .ok after) :
    loadDWord (toMemory after.shared.resources.space) record.config.dataAddress = .ok value := by
  obtain ⟨actual, result, selected, stored, same⟩ := guardStore_ok _ _ _ _ _ success
  have equal := Except.ok.inj (selected.symm.trans authorized)
  subst actual
  have noTicket := store_none stored
  have storedNone : Borrowing.mutate state.shared (.store record.config.owner record.config.dataTicket record.config.dataAddress value) = .ok (result.1, none) := by
    rw [← noTicket]
    exact stored
  rw [same]
  exact (store_effect storedNone).readback

/-- An initially unlocked, valid registration always admits an acquiring
attempt. Busy/reentrant attempts remain separate successful RMW outcomes. -/
theorem acquire_free (state : State) (actor : Nat) (record : Registered)
    (valid : WellFormed state) (live : state.mutex = some record) (free : record.holder = none) :
    ∃ result lease current, tryAcquire state actor = .ok result ∧ result.acquired = some lease ∧
      authorize result.state actor lease = .ok current ∧ current.config = record.config ∧
      Closed result.state.shared current.config := by
  obtain ⟨result, success⟩ := tryAcquire_enabled state actor record valid live
  obtain ⟨actual, exchanged, found, exchange, branches⟩ := tryAcquire_ok _ _ _ success
  have equal := Option.some.inj (found.symm.trans live)
  subst actual
  have phase := (valid.2 _ live).phase
  rw [free] at phase
  have actual := (AtomicExchange.exchangeWord_sound _ _ _ _ _ _ exchange).2.2.1
  have zero := Except.ok.inj (actual.symm.trans phase.1)
  rcases branches with ⟨_, same⟩ | ⟨busy, _⟩
  · let lease : Lease := ⟨state.nextLease, actor⟩
    let current : Registered := { record with holder := some lease }
    have authorized : authorize result.state actor lease = .ok current := by
      rw [same]
      apply authorize_of_held <;> rfl
    obtain ⟨value, observed, invariant⟩ := phase.2
    have data := exchange_data _ _ _ _ valid live exchange
    refine ⟨result, lease, current, success, ?_, authorized, rfl, ?_⟩
    · rw [same]
    · rw [same]; exact ⟨value, data.trans observed, invariant⟩
  · exact False.elim (busy zero)

/-- A genuine finite critical-section cycle exists for every admitted unlocked
state and any temporary/final values whose final value satisfies the independent
payload invariant. The temporary store need not satisfy it. This proves no
fairness, native call/runtime correspondence, or arbitrary-scheduler progress. -/
theorem critical_cycle (state : State) (actor : Nat) (record : Registered)
    (temporary value : BitVec 32) (valid : WellFormed state) (live : state.mutex = some record)
    (free : record.holder = none) (closed : record.config.invariant value = true) :
    ∃ acquired lease intermediate written result,
      tryAcquire state actor = .ok acquired ∧ acquired.acquired = some lease ∧
      guardStore acquired.state actor lease temporary = .ok intermediate ∧
      guardStore intermediate actor lease value = .ok written ∧
      release written actor lease = .ok result ∧ WellFormed result.1 ∧ Revoked result.1 lease ∧
      loadDWord (toMemory result.1.shared.resources.space) record.config.dataAddress = .ok value := by
  obtain ⟨acquired, lease, current, attempt, granted, authorized, configEq, _⟩ := acquire_free state actor record valid live free
  have acquiredValid := tryAcquire_wellFormed _ _ _ valid attempt
  obtain ⟨intermediate, first⟩ := guardStore_enabled acquired.state actor lease temporary current acquiredValid authorized
  have intermediateValid := guardStore_wellFormed _ _ _ _ _ acquiredValid first
  have intermediateAuth := guardStore_authorized _ _ _ _ _ _ authorized first
  obtain ⟨written, second⟩ := guardStore_enabled intermediate actor lease value current intermediateValid intermediateAuth
  have writtenValid := guardStore_wellFormed _ _ _ _ _ intermediateValid second
  have writtenAuth := guardStore_authorized _ _ _ _ _ _ intermediateAuth second
  have observed := guardStore_value _ _ _ _ _ _ intermediateAuth second
  have finalInvariant : current.config.invariant value = true := by simpa only [configEq] using closed
  obtain ⟨result, released⟩ := release_enabled written actor lease current writtenValid writtenAuth ⟨value, observed, finalInvariant⟩
  obtain ⟨actual, _, exchanged, selected, _, _, exchange, same⟩ := release_ok _ _ _ _ released
  have equal := Except.ok.inj (selected.symm.trans writtenAuth)
  subst actual
  have data := exchange_data _ _ _ _ writtenValid (authorize_ok _ _ _ _ writtenAuth).1 exchange
  refine ⟨acquired, lease, intermediate, written, result, attempt, granted, first, second, released,
    release_wellFormed _ _ _ _ writtenValid released, release_revokes _ _ _ _ writtenValid released, ?_⟩
  rw [same]
  simpa only [configEq] using data.trans observed

end EDSL.OS.Mutex
