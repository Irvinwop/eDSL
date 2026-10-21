/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.PlainCallAdmission64
import EDSL.OS.PlainCallBehavior64
import EDSL.OS.TSO64.Stability
import EDSL.OS.TSO64.C23Projection.AtomicTrace.FromSchedule
import EDSL.X86.VCGen.PlainMethods.History

/-!
Closed plain-call histories from independent present-state admission and an
actual finished production execution. Initial registry/RAM enumeration and
successful scanning are derived from current resources and that same run.
Static checked catalog shapes are needed only for the method/call adapter.

The complete initialized registry, original action positions, actual source
keys, full64 words and all managed publications are retained by the existing
capture and graph correspondence. Per-slot sites, targets, actors, counters
and logical occurrence labels may differ. Initial/final queues are empty
boundaries; an individual store may return before its later publication.

These results expose the modeled finite atomic-fragment History, including
the same independent completed behavior and call list. They do not define a
full independent Claim or final-file
certificate, extend history to nonempty incoming queues, infer language orders
from bytes, or establish compiler/native/kernel/lifecycle/fairness guarantees.
-/

set_option autoImplicit false

namespace EDSL.OS.PlainCallHistory64
open X86 TSO64 Grading.ConcurrentTask.Plain64
open TSO64.C23Projection X86.VCGen Concurrency

/-- Independent ClosedPre remains current-only. The successful scan and all
initialized values are outputs of its resources and the actual execution.
No static method shape is needed just to obtain raw capture. -/
theorem captured_of_closed {catalog : Catalog} {initial : TSO64.State}
    {inputs : Fin initial.workers.length → Input} (pre : ClosedPre catalog initial inputs)
    {actions : List Action} {result : TSO64.State × List Observation}
    (success : schedule initial actions .sharedCell = .ok result)
    (finished : Finished result.1) (offset : Nat) :
    ∃ (run : AtomicTrace.Result) (initials : List AtomicTrace.Initials.Entry),
      run.execution = result ∧
      AtomicTrace.Graph.Captured initial actions .sharedCell offset run initials :=
  AtomicTrace.Graph.captured_of_schedule pre.1.valid pre.2 success finished.2 offset

/-- Separate static shapes discharge only the method-to-call adapter. Raw
capture, executable graph construction and modeled legality are outputs.
Every actual original slot supplies its real completed call, not a desired
reply, later cutpoint, initializer subset or assumed source/history graph. -/
theorem history_of_closed {catalog : Catalog} (static : PlainCallAdmission64.StaticShapes catalog)
    {initial : TSO64.State} {inputs : Fin initial.workers.length → Input}
    (pre : ClosedPre catalog initial inputs)
    {actions : List Action} {result : TSO64.State × List Observation}
    (success : schedule initial actions .sharedCell = .ok result)
    (finished : Finished result.1) (offset : Nat) :
    ∃ (run : AtomicTrace.Result) (initials : List AtomicTrace.Initials.Entry),
      run.execution = result ∧
      AtomicTrace.Graph.Captured initial actions .sharedCell offset run initials ∧
      ∃ table,
        AtomicTrace.Graph.build (AtomicTrace.Graph.runInputs initials run offset)
          PlainMethods.AtomicEvents.orders = some table ∧
        AtomicTrace.Graph.Built (AtomicTrace.Graph.runInputs initials run offset)
          PlainMethods.AtomicEvents.orders table ∧
        ∃ batch : PlainMethods.BatchResult initial actions run.execution
            (PlainCallAdmission64.invocations static pre.1),
          AtomicCalls.History (initials.map AtomicTrace.Graph.initialEvent)
            batch.calls table.toCandidate := by
  obtain ⟨run, initials, execution, captured⟩ := captured_of_closed pre success finished offset
  have returned : ∀ tid : Fin initial.workers.length,
      ∃ final, run.state.workers[tid.val]? = some final ∧ final.phase = .returned := by
    intro tid
    obtain ⟨original, originalLive, _facts⟩ := pre.1.entry tid
    obtain ⟨final, finalLive, _resources⟩ := schedule_worker_resources success originalLive
    have stateEq : run.state = result.1 := congrArg Prod.fst execution
    refine ⟨final, ?_, finished.1 final (List.mem_of_getElem? finalLive)⟩
    rw [stateEq]
    exact finalLive
  obtain ⟨table, built, batch, history⟩ :=
    PlainMethods.Correspondence.history captured
      (PlainCallAdmission64.invocations static pre.1) returned
  exact ⟨run, initials, execution, captured, table, built,
    AtomicTrace.Graph.build_sound built, batch, history⟩

/-- The independently specified completed behavior and the constructed atomic
history describe exactly the same actual call list. This adapter performs the
dependent execution/reply transports once for every supported catalog. -/
theorem behavior_history_of_closed {catalog : Catalog}
    (static : PlainCallAdmission64.StaticShapes catalog)
    {initial : TSO64.State} {inputs : Fin initial.workers.length → Input}
    (pre : ClosedPre catalog initial inputs)
    {actions : List Action} {result : TSO64.State × List Observation}
    (success : schedule initial actions .sharedCell = .ok result)
    (finished : Finished result.1) (offset : Nat) :
    ∃ (run : AtomicTrace.Result) (initials : List AtomicTrace.Initials.Entry),
      run.execution = result ∧
      AtomicTrace.Graph.Captured initial actions .sharedCell offset run initials ∧
      ∃ table,
        AtomicTrace.Graph.build (AtomicTrace.Graph.runInputs initials run offset)
          PlainMethods.AtomicEvents.orders = some table ∧
        AtomicTrace.Graph.Built (AtomicTrace.Graph.runInputs initials run offset)
          PlainMethods.AtomicEvents.orders table ∧
        ∃ post : Post initial inputs actions result,
          AtomicCalls.History (initials.map AtomicTrace.Graph.initialEvent)
            post.calls table.toCandidate := by
  obtain ⟨run, initials, execution, captured, table, built, mapped, batch, history⟩ :=
    history_of_closed static pre success finished offset
  subst result
  obtain ⟨post, calls⟩ :=
    PlainCallBehavior64.post_of_batch static pre.1 batch finished.1
  refine ⟨run, initials, rfl, captured, table, built, mapped, post, ?_⟩
  rw [calls]
  exact history

end EDSL.OS.PlainCallHistory64

#audit_edsl
