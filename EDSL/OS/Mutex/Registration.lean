/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Mutex.Facts

namespace EDSL.OS.Mutex
open X86 AddressSpace

theorem register_ok (state : State) (config : Config) (after : State)
    (valid : Borrowing.WellFormed state.shared) (success : register state config = .ok after) :
    state.mutex = none ∧ config.lockTicket.identifier ≠ config.dataTicket.identifier ∧
      WordValid state.shared config.owner config.lockTicket config.lockAddress ∧
      WordValid state.shared config.owner config.dataTicket config.dataAddress ∧
      atomicAddressable config.lockAddress = true ∧ NoReaders state.shared config ∧
      loadDWord (toMemory state.shared.resources.space) config.lockAddress = .ok 0 ∧
      Closed state.shared config ∧ after = { state with mutex := some ⟨config, none⟩ } := by
  cases present : state.mutex with
  | some record => simp [register, present] at success
  | none =>
    by_cases sameId : config.lockTicket.identifier = config.dataTicket.identifier
    · simp [register, present, sameId] at success
    · cases lockAuth : Ownership.authorize state.shared.resources config.owner config.lockTicket with
      | error fault => simp [register, present, sameId, lockAuth, Except.mapError] at success
      | ok lock =>
        cases dataAuth : Ownership.authorize state.shared.resources config.owner config.dataTicket with
        | error fault => simp [register, present, sameId, lockAuth, dataAuth, Except.mapError] at success
        | ok data =>
          by_cases lockFits : Ownership.containsWord lock config.lockAddress = true
          · by_cases dataFits : Ownership.containsWord data config.dataAddress = true
            · by_cases supported : atomicAddressable config.lockAddress = true
              · by_cases lockWritable : canStoreDWord (toMemory state.shared.resources.space) config.lockAddress = true
                · by_cases dataWritable : canStoreDWord (toMemory state.shared.resources.space) config.dataAddress = true
                  · by_cases lockLoans : Borrowing.allowed state.shared (.store config.owner config.lockTicket config.lockAddress 0) = true
                    · simp only [BitVec.ofNat_eq_ofNat] at lockLoans
                      by_cases dataLoans : Borrowing.allowed state.shared (.store config.owner config.dataTicket config.dataAddress 0) = true
                      · simp only [BitVec.ofNat_eq_ofNat] at dataLoans
                        cases lockRead : loadDWord (toMemory state.shared.resources.space) config.lockAddress with
                        | error fault =>
                          simp [register, present, sameId, lockAuth, dataAuth, lockFits, dataFits,
                            supported, lockWritable, dataWritable, lockLoans, dataLoans, lockRead, Except.mapError] at success
                        | ok old =>
                          by_cases zero : old = 0
                          · simp only [BitVec.ofNat_eq_ofNat] at zero
                            cases dataRead : loadDWord (toMemory state.shared.resources.space) config.dataAddress with
                            | error fault =>
                              simp [register, present, sameId, lockAuth, dataAuth, lockFits, dataFits,
                                supported, lockWritable, dataWritable, lockLoans, dataLoans, lockRead, zero, dataRead, Except.mapError] at success
                            | ok value =>
                              by_cases invariant : config.invariant value = true
                              · simp [register, present, sameId, lockAuth, dataAuth, lockFits, dataFits,
                                  supported, lockWritable, dataWritable, lockLoans, dataLoans, lockRead, zero, dataRead, invariant, Except.mapError] at success
                                obtain ⟨lockAt, lockOwner, lockEpoch⟩ := Ownership.authorize_ok _ _ _ _ lockAuth
                                obtain ⟨dataAt, dataOwner, dataEpoch⟩ := Ownership.authorize_ok _ _ _ _ dataAuth
                                refine ⟨rfl, sameId, ⟨lock, lockAt, lockOwner, lockEpoch, lockFits, lockWritable⟩,
                                  ⟨data, dataAt, dataOwner, dataEpoch, dataFits, dataWritable⟩,
                                  supported, ?_, by simp only [zero, BitVec.ofNat_eq_ofNat],
                                  ⟨value, dataRead, invariant⟩, success.symm⟩
                                intro identifier loan live
                                constructor
                                · have excluded := Borrowing.allowed_sound _ _ valid lockLoans identifier loan live
                                  simpa [Ownership.Mutation.target, eq_comm] using excluded
                                · have excluded := Borrowing.allowed_sound _ _ valid dataLoans identifier loan live
                                  simpa [Ownership.Mutation.target, eq_comm] using excluded
                              · simp [register, present, sameId, lockAuth, dataAuth, lockFits, dataFits,
                                  supported, lockWritable, dataWritable, lockLoans, dataLoans, lockRead, zero, dataRead, invariant, Except.mapError] at success
                          · simp only [BitVec.ofNat_eq_ofNat] at zero
                            simp [register, present, sameId, lockAuth, dataAuth, lockFits, dataFits,
                              supported, lockWritable, dataWritable, lockLoans, dataLoans, lockRead, zero, Except.mapError] at success
                      · simp only [BitVec.ofNat_eq_ofNat] at dataLoans
                        simp [register, present, sameId, lockAuth, dataAuth, lockFits, dataFits,
                          supported, lockWritable, dataWritable, lockLoans, dataLoans, Except.mapError] at success
                    · simp only [BitVec.ofNat_eq_ofNat] at lockLoans
                      simp [register, present, sameId, lockAuth, dataAuth, lockFits, dataFits,
                        supported, lockWritable, dataWritable, lockLoans, Except.mapError] at success
                  · simp [register, present, sameId, lockAuth, dataAuth, lockFits, dataFits,
                      supported, lockWritable, dataWritable, Except.mapError] at success
                · simp [register, present, sameId, lockAuth, dataAuth, lockFits, dataFits,
                    supported, lockWritable, Except.mapError] at success
              · simp [register, present, sameId, lockAuth, dataAuth, lockFits, dataFits,
                  supported, Except.mapError] at success
            · simp [register, present, sameId, lockAuth, dataAuth, dataFits, Except.mapError] at success
          · simp [register, present, sameId, lockAuth, dataAuth, lockFits, Except.mapError] at success

theorem register_wellFormed (state : State) (config : Config) (after : State)
    (valid : WellFormed state) (success : register state config = .ok after) : WellFormed after := by
  obtain ⟨_, separate, lock, data, atomic, readers, observed, closed, same⟩ :=
    register_ok _ _ _ valid.1 success
  rw [same]
  refine ⟨valid.1, ?_⟩
  intro record live
  simp only [Option.some.injEq] at live
  cases live
  exact ⟨lock, data, separate, atomic, readers, observed, closed⟩

end EDSL.OS.Mutex
