/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.ServiceFrames

namespace EDSL.OS.Futex

theorem service_storage {config : Config} {state after : State} {action : Action}
    (success : step config state action = .ok after) :
    after.suspended.machine.memory = state.suspended.machine.memory ∧
      after.authority.shared = state.authority.shared ∧ Atomics.History state.authority after.authority :=
  ⟨service_memory success, service_shared success, service_resources_history success⟩

end EDSL.OS.Futex
