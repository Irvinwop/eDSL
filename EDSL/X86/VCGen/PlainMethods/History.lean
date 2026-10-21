/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.PlainMethods.Correspondence
import EDSL.OS.TSO64.C23Projection.AtomicTrace.GraphConstruction

/-!
Completed plain-method histories from raw initialized machine scans. The
executable graph builder, its legality proof and the complete call/event
correspondence all refer to the same scan. Neither a proposed graph nor an
event-list equality, source selection or rank is an admission input.

The boundary admits one invocation per actual initial worker slot, with empty
initial and final queues. Stores may return before their later publication;
the graph uses publication positions rather than access or RET positions for
modification ranks. Scanner offsets, machine store counters, logical occurrence
labels and full 64-bit words retain their existing independent meanings.

This is the modeled finite atomic-fragment History contract with the existing
sharedCell scalar-RAM, long-mode/CET-off, authority, translation/alias, code and
protected-caller boundaries of Captured and Invocation. Acquire/release are
declared interface orders. It supplies no repeated-invocation, worker-creation,
full C23, source/compiler, native CPU/kernel or fairness guarantee.
-/

set_option autoImplicit false

namespace EDSL.X86.VCGen.PlainMethods.Correspondence
open OS OS.TSO64 OS.TSO64.C23Projection Concurrency

variable {initial : OS.TSO64.State} {actions : List Action} {run : AtomicTrace.Result}
  {offset : Nat} {initials : List AtomicTrace.Initials.Entry}
  {invocations : (tid : Fin initial.workers.length) → Invocation initial tid.val}

/-- Construct the actual graph for an already extracted batch. Initializer
shape follows from the graph's initializer representation; exact call/event
equality is the existing scanner correspondence theorem. Legality is derived
from the raw captured run rather than supplied by the caller. -/
theorem history_of_batch
    (captured : AtomicTrace.Graph.Captured initial actions .sharedCell offset run initials)
    (batch : BatchResult initial actions run.execution invocations) :
    ∃ table,
      AtomicTrace.Graph.build (AtomicTrace.Graph.runInputs initials run offset)
        AtomicEvents.orders = some table ∧
      AtomicCalls.History (initials.map AtomicTrace.Graph.initialEvent)
        batch.calls table.toCandidate := by
  obtain ⟨table, built, executed, legal⟩ := captured.build_legal AtomicEvents.orders
  refine ⟨table, built, ?_, legal⟩
  apply realizes batch captured.valid captured.sequenced captured.scanned
  · change table.events = initials.map AtomicTrace.Graph.initialEvent ++
      run.events.map (fun actual => actual.toSource AtomicEvents.orders)
    simpa only [AtomicTrace.Graph.sourceEvents, AtomicTrace.Graph.runInputs] using
      executed.mapped.events_eq
  · intro actual member
    obtain ⟨entry, _, rfl⟩ := List.mem_map.mp member
    exact ⟨rfl, entry.value, rfl⟩

/-- Raw initialized scan + one present admitted invocation per actual initial
worker + final returned workers construct both the complete call batch and the
actual executable builder's History. Final replies, access/RET cutpoints and
all graph metadata are conclusions. Empty queues are only endpoint boundaries;
there is no requirement that a store publish before its own RET. -/
theorem history
    (captured : AtomicTrace.Graph.Captured initial actions .sharedCell offset run initials)
    (invocations : (tid : Fin initial.workers.length) → Invocation initial tid.val)
    (returned : ∀ tid : Fin initial.workers.length,
      ∃ final, run.state.workers[tid.val]? = some final ∧ final.phase = .returned) :
    ∃ table,
      AtomicTrace.Graph.build (AtomicTrace.Graph.runInputs initials run offset)
        AtomicEvents.orders = some table ∧
      ∃ batch : BatchResult initial actions run.execution invocations,
        AtomicCalls.History (initials.map AtomicTrace.Graph.initialEvent)
          batch.calls table.toCandidate := by
  have scheduled : schedule initial actions .sharedCell = .ok run.execution :=
    captured.certificate.scheduled
  have returnedExecution : ∀ tid : Fin initial.workers.length,
      ∃ final, run.execution.1.workers[tid.val]? = some final ∧ final.phase = .returned := by
    simpa only [AtomicTrace.Result.execution] using returned
  obtain ⟨batch⟩ := completed_batch invocations scheduled returnedExecution
  obtain ⟨table, built, accepted⟩ := history_of_batch captured batch
  exact ⟨table, built, batch, accepted⟩

end EDSL.X86.VCGen.PlainMethods.Correspondence

#print axioms EDSL.X86.VCGen.PlainMethods.Correspondence.history_of_batch
#print axioms EDSL.X86.VCGen.PlainMethods.Correspondence.history
#audit_edsl
