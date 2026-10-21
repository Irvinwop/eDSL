/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.PlainCall64
import tests.PlainCallHistory64

/-!
Clients of independent completed behavior over actual nonempty executions.
The open client keeps both mixed incoming FIFOs and returned stores pending;
collection must still fail. The closed client requires the independently
specified Post and constructed History to describe the same actual call list,
then checks the full64 old read and persistent INITIAL source against the real
scanner. The writer returned before the actual publication, so treating RET as
publication would violate this expected read source. Resource installation and
execution are shared existing fixtures, not repeated instruction proofs.
-/

set_option autoImplicit false

namespace EDSL.Tests.PlainCallBehavior64
open X86 OS.TSO64 OS.TSO64.C23Projection Concurrency
open Grading.ConcurrentTask

/-- Returning the independently specified calls leaves both original mixed
incoming queues represented. Store return alone cannot enable collection. -/
theorem open_behavior :
    Nonempty (Plain64.Post PlainCallAdmission64.initial PlainCallAdmission64.inputs
      PlainCallAdmission64.actions PlainCallAdmission64.result) ∧
    collect PlainCallAdmission64.result.1 0 = .error .resource ∧
    collect PlainCallAdmission64.result.1 1 = .error .resource := by
  refine ⟨OS.PlainCallBehavior64.post PlainCallAdmission64.separateStaticShapes
    PlainCallAdmission64.independentPre PlainCallAdmission64.scheduled
    PlainCallAdmission64.result_returned, ?_, ?_⟩
  · exact PlainCallAdmission64.actual_read_and_deferred_store.2.2.2.2.2.2.2.2.2.2.1
  · exact PlainCallAdmission64.actual_read_and_deferred_store.2.2.2.2.2.2.2.2.2.2.2

/-- Current closed resources and the actual Finished execution supply both the
independent completed Post and legal History with literally the same calls.
The expected read source is INITIAL even though the writer has already RET'd. -/
theorem closed_behavior_history :
    ∃ (run : AtomicTrace.Result) (initials : List AtomicTrace.Initials.Entry)
      (table : AtomicTrace.Graph.Table)
      (post : Plain64.Post PlainCallHistory64.initial PlainCallHistory64.inputs
        PlainCallHistory64.actions PlainCallHistory64.result),
      run.execution = PlainCallHistory64.result ∧
      AtomicTrace.Graph.build (AtomicTrace.Graph.runInputs initials run 37)
        X86.VCGen.PlainMethods.AtomicEvents.orders = some table ∧
      AtomicCalls.History (initials.map AtomicTrace.Graph.initialEvent)
        post.calls table.toCandidate ∧
      run.events =
        [⟨37, 1, .store PlainCallHistory64.writerReference PlainCallAdmission64.storeWord 11⟩,
         ⟨39, 0, .load PlainCallHistory64.readerReference PlainCallAdmission64.oldWord
           (.initial PlainCallAdmission64.target)⟩] := by
  obtain ⟨run, initials, execution, captured, table, built, _mapped, post, history⟩ :=
    OS.PlainCallHistory64.behavior_history_of_closed PlainCallAdmission64.separateStaticShapes
      PlainCallHistory64.independentClosedPre PlainCallHistory64.scheduled
      PlainCallHistory64.finished 37
  have expected := PlainCallHistory64.literal_scan
  rw [captured.scanned] at expected
  exact ⟨run, initials, table, post, execution, built, history, Except.ok.inj expected⟩

end EDSL.Tests.PlainCallBehavior64

#print axioms EDSL.Tests.PlainCallBehavior64.open_behavior
#print axioms EDSL.Tests.PlainCallBehavior64.closed_behavior_history
#audit_edsl
