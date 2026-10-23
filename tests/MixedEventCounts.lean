/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.MixedResumableBlocking
import EDSL.OS.TSO64.EffectSimulation.Mixed.Counts

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
The independently admitted INC/RET client and its actual interleaved execution
contain one RMW from each worker. Peer XADD(+4) is one retirement, while both
blocked attempts, both drains and the own RET contribute none. The full seven
positions remain in the trace. These expected counts follow the two routines'
executed instructions, independently of the counting implementation.
-/

namespace EDSL.Tests.MixedEventCounts
open OS.TSO64.EffectSimulation
open Mixed
open MixedResumableBlocking

/-- Count actual native observations, including the blocked/drain positions,
rather than inferring a count from the modular change in the shared word. -/
theorem independent_interleaved_counts :
    ∃ (fixture : Fixture) (final : S)
      (ghost : Ghost (descriptor fixture) fixture.state (returnPost fixture)),
      Integration fixture final ghost ∧
      Counts.logRMW 0 ghost.history = 1 ∧
      Counts.logRMW 1 ghost.history = 1 ∧
      ghost.history.length = 7 := by
  obtain ⟨fixture, final, ghost, integrated⟩ := independent_integration
  refine ⟨fixture, final, ghost, integrated, ?_, ?_, integrated.sevenPositions⟩
  all_goals
    rw [Counts.logRMW, integrated.observationPositions]
    simp [expectedObservations, Counts.countRMW, Counts.ownRMW]

end EDSL.Tests.MixedEventCounts

#print axioms EDSL.Tests.MixedEventCounts.independent_interleaved_counts
#audit_edsl
