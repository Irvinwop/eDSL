/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.ConcurrentTask.Plain64.History
import EDSL.OS.PlainCallBehavior64
import EDSL.X86.VCGen.PlainMethods.Correspondence

/-!
Alignment of the existing actual batch with the independent completed Post.
The exact call-list equality exported by `post_of_batch` identifies each slot
through actual thread uniqueness. Initial workers and full managed references
are identified separately by actual liveness and the original atomic selector.
No equality of payload bits is used to select a reference or read-source key.
-/

set_option autoImplicit false

namespace EDSL.OS.PlainCallBehavior64
open X86 TSO64 Grading.ConcurrentTask.Plain64
open TSO64.C23Projection X86.VCGen Concurrency
open PlainCallAdmission64

theorem outcome_initial {input : Input} {before : TSO64.State} {tid : Nat}
    (admitted : Admitted input before tid) {actions : List Action}
    {actual : TSO64.State × List Observation}
    (output : Outcome input before actions actual tid) :
    output.initial = admitted.invocation.initial :=
  Option.some.inj (output.initialLive.symm.trans admitted.invocation.live)

private theorem reference_tuple {first second : Queue.ManagedRef}
    (same : (first.identifier, first.handle, first.cell) =
      (second.identifier, second.handle, second.cell)) : first = second := by
  have identifier := congrArg Prod.fst same
  have descriptor := congrArg Prod.snd same
  have handle := congrArg Prod.fst descriptor
  have cell := congrArg Prod.snd descriptor
  cases first
  cases second
  cases identifier
  cases handle
  cases cell
  rfl

/-- Deterministic selection identifies the entire original descriptor, even
when another handle, address or word could otherwise look identical. -/
theorem outcome_reference {input : Input} {before : TSO64.State} {tid : Nat}
    (admitted : Admitted input before tid) {actions : List Action}
    {actual : TSO64.State × List Observation}
    (output : Outcome input before actions actual tid) :
    output.reference = admitted.invocation.method.reference := by
  have selected := output.originalSelection
  rw [outcome_initial admitted output] at selected
  exact reference_tuple (Option.some.inj (selected.symm.trans admitted.selected))

private theorem call_reply_heq
    {first second : AtomicCalls.Call Atomics64.CellId64 Word} (same : first = second) :
    HEq first.reply second.reply := by
  cases same
  exact HEq.rfl

private theorem request_transport_heq (input : Input) {operation : PlainMethods.Operation}
    (same : operation = fixedOperation input.site.kind) (object : Atomics64.CellId64)
    (entry : Register → Word) (reply : operation.Reply) :
    HEq (operation.requestReply object entry reply) (transportReply input same reply) := by
  cases input <;> cases same <;> exact HEq.rfl

/-- Reply alignment retains the actual completed-call reply. The call equality
is the output of `post_of_batch`, whose same-run access/read and RET uniqueness
proofs already connect this datum to the production execution. -/
theorem outcome_completed_reply {input : Input} {before : TSO64.State} {tid : Nat}
    (admitted : Admitted input before tid) {actions : List Action}
    {actual : TSO64.State × List Observation}
    (output : Outcome input before actions actual tid)
    (completed : PlainMethods.CompletedCall admitted.invocation.method tid before actions actual)
    (same : output.call = completed.call admitted.invocation.occurrence) :
    output.reply = transportReply input admitted.operation completed.reply := by
  have actualReply : HEq output.reply
      (admitted.invocation.method.operation.requestReply
        admitted.invocation.method.reference.handle.cell admitted.invocation.method.entry
        completed.reply) := call_reply_heq same
  exact eq_of_heq (actualReply.trans
    (request_transport_heq input admitted.operation _ _ completed.reply))

private theorem access_transport (input : Input) {operation : PlainMethods.Operation}
    (same : operation = fixedOperation input.site.kind) {initial : Worker}
    {entry : Register → Word} {counter : Nat}
    (original : entry = initial.context.registers) (count : counter = initial.nextStore)
    (arguments : Arguments input initial) (reference : Queue.ManagedRef)
    (reply : operation.Reply) (source : AtomicTrace.WriterId) :
    PlainMethods.AtomicEvents.access operation reference entry counter source reply =
      match input with
      | .loadAcquire image object cell occurrence =>
          .load reference (transportReply (.loadAcquire image object cell occurrence) same reply) source
      | .storeRelease _ _ _ value _ => .store reference value initial.nextStore := by
  cases input with
  | loadAcquire image target cell occurrence =>
    cases same
    rfl
  | storeRelease image target cell value occurrence =>
    cases same
    change AtomicTrace.Access.store reference (entry .rsi) counter =
      .store reference value initial.nextStore
    rw [original, arguments.store_rsi, count]

/-- Exact event alignment, before source erasure. Original-position equality
comes from the actual call; the reference, saved counter and full64 source
register are transported from original admission rather than guessed. -/
theorem outcome_machineEvent {input : Input} {before : TSO64.State} {tid : Nat}
    (admitted : Admitted input before tid) {actions : List Action}
    {actual : TSO64.State × List Observation}
    (output : Outcome input before actions actual tid)
    (completed : PlainMethods.CompletedCall admitted.invocation.method tid before actions actual)
    (same : output.call = completed.call admitted.invocation.occurrence)
    (source : AtomicTrace.WriterId) (offset : Nat) :
    output.machineEvent source offset = PlainMethods.AtomicEvents.event
      admitted.invocation.method tid (offset + completed.performed) completed.reply source := by
  have initial := outcome_initial admitted output
  have reference := outcome_reference admitted output
  have performed : output.performed = completed.performed :=
    congrArg AtomicCalls.Call.performed same
  have reply := outcome_completed_reply admitted output completed same
  have access := access_transport input admitted.operation admitted.registers admitted.counter
    admitted.entryFacts.arguments admitted.invocation.method.reference completed.reply source
  cases input with
  | loadAcquire image target cell occurrence =>
    change (⟨offset + output.performed, tid,
      .load output.reference output.reply source⟩ : AtomicTrace.Event) =
      ⟨offset + completed.performed, tid,
        PlainMethods.AtomicEvents.access admitted.invocation.method.operation
          admitted.invocation.method.reference admitted.invocation.method.entry
          admitted.invocation.method.initialQueue.nextStore source completed.reply⟩
    rw [performed, reference, reply, access]
  | storeRelease image target cell value occurrence =>
    change (⟨offset + output.performed, tid,
      .store output.reference value output.initial.nextStore⟩ : AtomicTrace.Event) =
      ⟨offset + completed.performed, tid,
        PlainMethods.AtomicEvents.access admitted.invocation.method.operation
          admitted.invocation.method.reference admitted.invocation.method.entry
          admitted.invocation.method.initialQueue.nextStore source completed.reply⟩
    rw [performed, reference, initial, access]

/-- Exact whole-list call equality identifies a slot by its actual thread, not
its logical occurrence, target, source value or position in a chosen graph. -/
theorem post_slot_call {catalog : Catalog} (static : StaticShapes catalog)
    {before : TSO64.State} {inputs : Fin before.workers.length → Input}
    (pre : Pre catalog before inputs) {actions : List Action}
    {actual : TSO64.State × List Observation}
    (post : Post before inputs actions actual)
    (batch : PlainMethods.BatchResult before actions actual (invocations static pre))
    (same : post.calls = batch.calls) (tid : Fin before.workers.length) :
    (post.outcomes tid).call = batch.call tid := by
  have slot : tid ∈ post.slots := post.permutation.mem_iff.mpr (List.mem_finRange tid)
  have member : (post.outcomes tid).call ∈ post.calls :=
    List.mem_map.mpr ⟨tid, slot, rfl⟩
  rw [same] at member
  exact batch.thread_unique member (batch.call_mem tid) rfl

/-- The Post uses exactly the batch's original slot order. This follows from
the exported whole call equality and injective scheduler thread identities. -/
theorem post_slots {catalog : Catalog} (static : StaticShapes catalog)
    {before : TSO64.State} {inputs : Fin before.workers.length → Input}
    (pre : Pre catalog before inputs) {actions : List Action}
    {actual : TSO64.State × List Observation}
    (post : Post before inputs actions actual)
    (batch : PlainMethods.BatchResult before actions actual (invocations static pre))
    (same : post.calls = batch.calls) : post.slots = batch.slots := by
  apply (List.map_inj_right (f := fun tid : Fin before.workers.length => tid.val)
    (fun _ _ equal => Fin.ext equal)).mp
  have threads := congrArg
    (List.map (fun call : AtomicCalls.Call Atomics64.CellId64 Word => call.thread)) same
  simpa only [Post.calls, PlainMethods.BatchResult.calls, List.map_map, Function.comp_def,
    Outcome.call, PlainMethods.BatchResult.call, PlainMethods.CompletedCall.call] using threads

/-- The production scanner's entire full machine-event list is expressed using
the same independent Post and per-slot actual sources. These are scanner keys,
not sources reconstructed from equal payload lookups or erased source events. -/
theorem post_machine_events {catalog : Catalog} (static : StaticShapes catalog)
    {before : TSO64.State} {inputs : Fin before.workers.length → Input}
    (pre : Pre catalog before inputs) {actions : List Action} {run : AtomicTrace.Result}
    (post : Post before inputs actions run.execution)
    (batch : PlainMethods.BatchResult before actions run.execution (invocations static pre))
    (same : post.calls = batch.calls) {offset : Nat}
    {writers : PublishedHistory.Writers}
    (sequenced : Sequenced before)
    (scanned : AtomicTrace.scan before actions .sharedCell offset writers = .ok run) :
    ∃ sources : Fin before.workers.length → AtomicTrace.WriterId,
      run.events = post.slots.map
        (fun tid => (post.outcomes tid).machineEvent (sources tid) offset) := by
  obtain ⟨sources, events⟩ :=
    PlainMethods.Correspondence.machine_events batch pre.valid sequenced scanned
  refine ⟨sources, ?_⟩
  rw [events, ← post_slots static pre post batch same]
  apply List.map_congr_left
  intro tid _member
  exact (outcome_machineEvent (admission static pre tid) (post.outcomes tid)
    (batch.completed tid) (post_slot_call static pre post batch same tid)
    (sources tid) offset).symm

end EDSL.OS.PlainCallBehavior64

#audit_edsl
