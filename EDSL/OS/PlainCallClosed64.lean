/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.ConcurrentTask.Plain64.History
import EDSL.OS.PlainCallBehavior64.Alignment
import EDSL.OS.PlainCallHistory64

/-!
Full closed-output transport from present independent admission, separately
checked static catalog shapes and the actual successful finished schedule.
Capture, complete initialized registry enumeration, actual source keys, the
entire machine-event list, executable graph construction and modeled History
are all derived. No desired source, graph, read result or scan success is an
admission hypothesis. Empty endpoint FIFOs leave allocation counters arbitrary.
-/

set_option autoImplicit false

namespace EDSL.OS.PlainCallClosed64
open X86 TSO64 Grading.ConcurrentTask.Plain64
open TSO64.C23Projection X86.VCGen Concurrency

/-- Empty actual incoming queues remove the incoming footprint from the full
independent prefix frame. Complete RAM cells are compared, not only readable
values or bytes selected by a particular load. -/
theorem memory_of_initialEmpty {before : TSO64.State}
    {inputs : Fin before.workers.length → Input} {actions : List Action}
    {actual : TSO64.State × List Observation} (post : Post before inputs actions actual)
    (empty : Quiescent before) :
    ∀ address, ¬Targets inputs address →
      actual.1.world.legacy.shared.resources.space.cells address =
        before.world.legacy.shared.resources.space.cells address := by
  intro address away
  apply post.safe.cells address
  rintro (target | incoming)
  · exact away target
  · obtain ⟨_tid, worker, entry, live, member, _inside⟩ := incoming
    have cleared := empty worker (List.mem_of_getElem? live)
    rw [cleared] at member
    cases member

/-- Collection uses this Post's actual final workers and the actual final
empty queues. RET and publication remain separate obligations. -/
theorem collection_of_finalEmpty {before : TSO64.State}
    {inputs : Fin before.workers.length → Input} {actions : List Action}
    {actual : TSO64.State × List Observation} (post : Post before inputs actions actual)
    (empty : Quiescent actual.1) :
    ∀ tid : Fin before.workers.length,
      collect actual.1 tid.val = .ok ((post.outcomes tid).final.context.registers .rax) := by
  intro tid
  exact (post.outcomes tid).frame.collectWhenEmpty
    (empty (post.outcomes tid).final
      (List.mem_of_getElem? (post.outcomes tid).frame.abi.live))

/-- Reusable full independent closed postcondition for every admitted catalog
and arbitrary actual finished run. The History uses literally the same Post's
calls; the machine equality retains full references, all full64 data, actual
allocation counters, source keys and original positions plus the given offset. -/
theorem post {catalog : Catalog} (static : PlainCallAdmission64.StaticShapes catalog)
    {before : TSO64.State} {inputs : Fin before.workers.length → Input}
    (pre : ClosedPre catalog before inputs) {actions : List Action}
    {actual : TSO64.State × List Observation}
    (success : schedule before actions .sharedCell = .ok actual)
    (finished : Finished actual.1) (offset : Nat := 0) :
    Nonempty (ClosedPost before inputs actions actual offset) := by
  obtain ⟨run, initials, execution, captured, table, built, mapped, batch, history⟩ :=
    PlainCallHistory64.history_of_closed static pre success finished offset
  subst actual
  obtain ⟨output, calls⟩ := PlainCallBehavior64.post_of_batch static pre.1 batch finished.1
  obtain ⟨sources, events⟩ := PlainCallBehavior64.post_machine_events static pre.1
    output batch calls captured.sequenced captured.scanned
  refine ⟨{
    calls := output
    run := run
    execution := rfl
    initials := initials
    captured := captured
    sources := sources
    machineEvents := events
    table := table
    built := built
    correspondence := mapped
    history := ?_
    memory := memory_of_initialEmpty output pre.2
    collection := collection_of_finalEmpty output finished.2 }⟩
  rw [calls]
  exact history

end EDSL.OS.PlainCallClosed64

#audit_edsl
