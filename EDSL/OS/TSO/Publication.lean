/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO.Drain
import EDSL.OS.TSO.Invariant

namespace EDSL.OS.TSO
open X86

theorem BuffersValid.pendingWritable {state : State} (valid : BuffersValid state) : PendingWritable state := by
  intro identifier worker live store member
  exact (valid worker (List.mem_of_getElem? live) store member).2.1

/-- Every queue reached from initial empty buffers has a concrete publication
path. The suffix length is the actual number of pending stores, including for
an already returned caller. No future successful action or drain fairness is
assumed. Publication retires no instructions and emits no new RMW event. -/
theorem publish_after_schedule (state : MachineThreads.State) (actions : List Action)
    (middle : State × List Observation) (identifier : Nat) (worker : Worker)
    (success : schedule (initial state) actions = .ok middle)
    (live : middle.1.workers[identifier]? = some worker) :
    ∃ result current,
      schedule middle.1 (List.replicate worker.buffer.length (.drain identifier)) = .ok result ∧
      result.1.workers[identifier]? = some current ∧ current.buffer = [] ∧
      current.context = worker.context ∧ current.returned = worker.returned ∧
      StoreBuffer.view result.1.memory current.buffer = StoreBuffer.view middle.1.memory worker.buffer ∧
      retiredCount result.2 = 0 ∧ atomicEvents result.2 = [] :=
  publish_worker worker.buffer.length middle.1 identifier worker
    (initial_schedule_buffers success).pendingWritable live rfl

end EDSL.OS.TSO
