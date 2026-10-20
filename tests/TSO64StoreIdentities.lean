/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.TSO64SharedCells
import EDSL.OS.TSO64.C23Projection.Origins
import EDSL.Audit

set_option autoImplicit false

namespace EDSL.Tests.TSO64StoreIdentities
open X86 OS.TSO64

/-- Bytes: MOV [RDI],RSI; MOV [RDI],RSI; RET. Both workers store zero, which
already occupies the shared cell. Draining a FIFO to empty must not reset its
issue counter, and another worker may independently use occurrence zero. -/
def start : Except Fault OS.TSO64.State :=
  TSO64SharedCells.start 0x00c3378948378948 0 0 0 0 0 0

def publications (observations : List Observation) : List (Nat × Nat × Nat × Word) :=
  observations.zipIdx |>.filterMap fun (observation, index) => match observation with
    | .drained tid (.managed _ value occurrence) => some (index, tid, occurrence, value)
    | _ => none

def counts (state : OS.TSO64.State) (tid : Nat) : Option (Nat × List Nat × Phase) :=
  state.workers[tid]?.map fun worker =>
    (worker.nextStore, Queue.occurrences worker.pending, worker.phase)

/-- Real decoding/admission/issue/drain/RET execution, with a peer issue between
same-thread stores and RET preceding the last drain. No expected IDs or source
edges are given to the scheduler. -/
def exercise : Except Fault
    (Option (Nat × List Nat × Phase) × Option (Nat × List Nat × Phase) ×
      List (Nat × Nat × Nat × Word) × Except Error Word × Except Error Word) := do
  let initial ← start
  let first ← schedule initial [.issue 0 false, .drain 0] .sharedCell
  let next ← schedule first.1 [.issue 1 false, .issue 0 true, .drain 1,
    .issue 0 false, .drain 0, .issue 1 true, .issue 1 false, .drain 1] .sharedCell
  pure (counts first.1 0, counts next.1 0, publications (first.2 ++ next.2),
    loadQWord (published next.1.world) 65536, loadQWord (published next.1.world) 65544)

/-- The queue empties after occurrence0; the next store still uses occurrence1.
Equal values and equal local occurrence numbers across threads remain distinct.
The untouched neighboring word is an independent memory-frame observation. -/
theorem empty_fifo_does_not_recycle_writer_identity : exercise = .ok
    (some (1, [], .running), some (2, [], .returned),
      [(1, 0, 0, 0), (4, 1, 0, 0), (6, 0, 1, 0), (9, 1, 1, 0)],
      .ok 0, .ok 0xabcdef0123456789) := by rfl

end EDSL.Tests.TSO64StoreIdentities

#print axioms EDSL.OS.TSO64.StoreHistory.IssuedAt.managed_identity_unique
#print axioms EDSL.OS.TSO64.StoreHistory.IssuedIn.published_of_quiescent
#print axioms EDSL.OS.TSO64.C23Projection.buffered_issue_unique
#audit_edsl
