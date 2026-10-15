/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexReplay

namespace EDSL.MutexWorkerCertificate
open X86 OS.AddressSpace OS.MutexReplay

def accepts (candidate : List Byte) : Bool := decide (candidate = bytes)

/-- Artifact admission is separate from finite-schedule admission. The latter
executes actual instructions and checks the independently stated endpoint.
No universal completion, enabledness or fairness claim is hidden here. -/
theorem sound (candidate : List Byte) (accepted : accepts candidate = true)
    (state : OS.MutexReplay.State) (selections : List Nat)
    (result : OS.MutexReplay.State × List (Nat × AtomicEvent))
    (verified : verify state selections = .ok result) :
    candidate = bytes ∧ ∃ record initial, state.shared.mutex = some record ∧
      loadDWord (toMemory state.shared.shared.resources.space) record.config.dataAddress = .ok initial ∧
      schedule state selections = .ok result ∧ Trace state selections result.2 result.1 ∧
      Post state result.1 initial :=
  ⟨of_decide_eq_true accepted, verify_sound _ _ _ verified⟩

end EDSL.MutexWorkerCertificate
