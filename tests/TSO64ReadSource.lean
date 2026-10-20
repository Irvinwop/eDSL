/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.TSO64SharedCells
import EDSL.OS.TSO64.ReadSource
import EDSL.OS.TSO64.ReadHistory
import EDSL.Audit

set_option autoImplicit false

namespace EDSL.Tests.TSO64ReadSource
open X86 OS.TSO64

/-- Observe the production forwarding position and its retained managed tag,
plus the real local and published reads. No expected source is fed to the CPU. -/
def source (state : OS.TSO64.State) (tid : Nat) (address : Word) :
    Option (Option (Nat × Nat × Word) × Except Error Word × Except Error Word) := do
  let worker ← state.workers[tid]?
  let selected := do
    let origin ← StoreBuffer.Mixed.newestQWord (payload worker.pending) address
    let .managed _ value occurrence ← worker.pending[origin.index]? | none
    pure (origin.index, occurrence, value)
  pure (selected, loadQWord (localCPU state worker).memory address,
    loadQWord (published state.world) address)

/-- Real MOV stores with equal values followed by actual FIFO publications.
The snapshot index changes on the first drain; the identity of the newest
issuing occurrence does not. The second drain removes forwarding entirely. -/
def equalValueSources : Except OS.TSO64.Fault
    (Option (Option (Nat × Nat × Word) × Except Error Word × Except Error Word) ×
     Option (Option (Nat × Nat × Word) × Except Error Word × Except Error Word) ×
     Option (Option (Nat × Nat × Word) × Except Error Word × Except Error Word) ×
     Option (Option (Nat × Nat × Word) × Except Error Word × Except Error Word)) := do
  let initial ← TSO64SharedCells.start 0x8b48378948378948 0x000000c3078b4807
    0x1122334455667788 0xfedcba9876543210 0 0 6
  let issued ← schedule initial [.issue 0 false, .issue 0 true] .sharedCell
  let first ← step issued.1 (.drain 0) .sharedCell
  let second ← step first.1 (.drain 0) .sharedCell
  pure (source issued.1 0 65536, source issued.1 1 65536,
    source first.1 0 65536, source second.1 0 65536)

theorem equal_values_keep_newest_issue_identity : equalValueSources = .ok
    (some (some (1, 1, 0xfedcba9876543210), .ok 0xfedcba9876543210, .ok 0x1122334455667788),
     some (none, .ok 0x1122334455667788, .ok 0x1122334455667788),
     some (some (0, 1, 0xfedcba9876543210), .ok 0xfedcba9876543210, .ok 0xfedcba9876543210),
     some (none, .ok 0xfedcba9876543210, .ok 0xfedcba9876543210)) := by rfl

end EDSL.Tests.TSO64ReadSource

#print axioms EDSL.OS.TSO64.newest_managed_entry
#print axioms EDSL.OS.TSO64.managed_read_source
#print axioms EDSL.OS.TSO64.OrdinaryEffect.managed_read_source
#print axioms EDSL.OS.TSO64.StoreHistory.schedule_pending_origin
#print axioms EDSL.OS.TSO64.StoreHistory.drain_after_schedule_issued
#print axioms EDSL.OS.TSO64.schedule_loadMem64_history
#print axioms EDSL.OS.TSO64.issue_ordinary_effect
#audit_edsl
