/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexReplay.Accounting
import EDSL.OS.MutexReplay.ProtocolFrame

namespace EDSL.OS.MutexReplay
open X86 AddressSpace

theorem dispatch_value (state : State) (config : Mutex.Config) (identifier : Nat) (worker : Worker)
    (result : State × Option AtomicEvent) (value : BitVec 32)
    (valid : Mutex.WellFormed state.shared) (registered : Registered state.shared config)
    (privateInv : WorkerInvariant state.shared config identifier worker)
    (live : state.workers[identifier]? = some worker)
    (observed : loadDWord (toMemory state.shared.shared.resources.space) config.dataAddress = .ok value)
    (success : dispatch state identifier = .ok result) :
    loadDWord (toMemory result.1.shared.shared.resources.space) config.dataAddress =
      .ok (value + BitVec.ofNat 32 (stores worker)) := by
  obtain ⟨actual, output, found, advanced, same⟩ := dispatch_ok _ _ _ success
  have equal := Option.some.inj (found.symm.trans live)
  subst actual
  obtain ⟨_, operation, selected, performed, _⟩ := advance_ok _ _ _ _ advanced
  rw [same]
  by_cases storing : ∃ lease, operation = .store lease
  · obtain ⟨lease, operationEq⟩ := storing
    subst operation
    obtain ⟨phases, held⟩ := action_store _ _ selected
    have payload := privateInv.payload lease held
    have beforeRead : loadDWord (toMemory state.shared.shared.resources.space) config.dataAddress =
        .ok (accumulator worker - 1) := by
      rcases phases with phase | phase <;> simp only [Payload, phase] at payload <;> exact payload.1
    have old := Except.ok.inj (observed.symm.trans beforeRead)
    cases perform_effect _ _ _ _ _ performed with
    | store guard record after context authorized operand stored ran =>
      have configEq := registered.config_eq (Mutex.authorize_ok _ _ _ _ authorized).1
      have afterRead := Mutex.guardStore_value _ _ _ _ _ _ authorized stored
      rw [configEq] at afterRead
      have count : stores worker = 1 := by simp [stores, phases]
      simpa [count, old, accumulator, BitVec.sub_add_cancel] using afterRead
  · have nonstore : ∀ guard, operation ≠ .store guard := by
      intro guard equal
      exact storing ⟨guard, equal⟩
    have frame := perform_data_frame _ _ _ _ _ _ valid registered nonstore performed
    have count := action_nonstore _ _ selected nonstore
    simpa [count] using frame.trans observed

end EDSL.OS.MutexReplay
