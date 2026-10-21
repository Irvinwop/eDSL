/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.ConcurrentTask.Plain64.Behavior
import EDSL.OS.TSO64.C23Projection.AtomicTrace.GraphConstruction

/-!
Independent whole-run observations for a closed plain64 call cohort. The
complete behavior, scanner execution, initialized live registry, full machine
events, actual source keys and constructed atomic History all describe the
same execution. Initial and final FIFOs are empty boundaries; counters and
full64 data are unrestricted, and a store may return before publication.

The declared acquire/release interface orders are not inferred from MOV bytes.
The graph's modeled finite atomic fragment retains the scalar-RAM, authority,
stable translation/no hidden aliases, long-mode/CET-off and fixed-population
boundaries of admission. This output contract makes no source/compiler,
physical CPU/kernel, lifecycle or fairness claim.
-/

set_option autoImplicit false

namespace EDSL.Grading.ConcurrentTask.Plain64
open X86 OS OS.TSO64 OS.TSO64.C23Projection Concurrency

/-- Independent annotations of the registered primitive interface. -/
def orders : AtomicTrace.Orders :=
  ⟨fun _ _ => .acquire, fun _ _ => .release, fun _ _ => .acqRel⟩

def model : String := "managed-tso64-plain64-cohort-v1"

/-- The full machine access, including its actual reference and allocation
counter. A source key matters for a load; stores have their own writer key.
The scanner offset changes positions, never machine allocation counters. -/
def Outcome.machineEvent {input : Input} {before : TSO64.State} {actions : List Action}
    {actual : TSO64.State × List Observation} {tid : Nat}
    (outcome : Outcome input before actions actual tid) (source : AtomicTrace.WriterId)
    (offset : Nat := 0) : AtomicTrace.Event :=
  ⟨offset + outcome.performed, tid, match input with
    | .loadAcquire .. => .load outcome.reference outcome.reply source
    | .storeRelease _ _ _ value _ =>
        .store outcome.reference value outcome.initial.nextStore⟩

theorem Outcome.machineEvent_toSource {input : Input} {before : TSO64.State}
    {actions : List Action} {actual : TSO64.State × List Observation} {tid : Nat}
    (outcome : Outcome input before actions actual tid) (source : AtomicTrace.WriterId)
    (offset : Nat := 0) :
    (outcome.machineEvent source offset).toSource orders = outcome.call.event := by
  cases input <;>
    simp only [Outcome.machineEvent, AtomicTrace.Event.toSource, AtomicTrace.Event.object,
      orders, Outcome.call, AtomicCalls.Call.event, Input.request,
      AtomicCalls.Request.object, AtomicCalls.Request.access, outcome.target, Input.target]

/-- Complete closed output. Neither capture, source keys, a desired graph nor
builder acceptance is an admission premise. The entire machine-event list is
specified in the same independent Post's slot order, with no erased payloads,
references, counters, actions or source identities. -/
structure ClosedPost (before : TSO64.State) (inputs : Fin before.workers.length → Input)
    (actions : List Action) (actual : TSO64.State × List Observation) (offset : Nat := 0) where
  calls : Post before inputs actions actual
  run : AtomicTrace.Result
  execution : run.execution = actual
  initials : List AtomicTrace.Initials.Entry
  captured : AtomicTrace.Graph.Captured before actions .sharedCell offset run initials
  sources : Fin before.workers.length → AtomicTrace.WriterId
  machineEvents : run.events = calls.slots.map
    (fun tid => (calls.outcomes tid).machineEvent (sources tid) offset)
  table : AtomicTrace.Graph.Table
  built : AtomicTrace.Graph.build (AtomicTrace.Graph.runInputs initials run offset) orders =
    some table
  correspondence : AtomicTrace.Graph.Built
    (AtomicTrace.Graph.runInputs initials run offset) orders table
  history : AtomicCalls.History (initials.map AtomicTrace.Graph.initialEvent)
    calls.calls table.toCandidate
  memory : ∀ address, ¬Targets inputs address →
    actual.1.world.legacy.shared.resources.space.cells address =
      before.world.legacy.shared.resources.space.cells address
  collection : ∀ tid : Fin before.workers.length,
    collect actual.1 tid.val = .ok ((calls.outcomes tid).final.context.registers .rax)

/-- Clients can read the entire declared call/event correspondence directly
from the independent closed output, preserving original execution positions. -/
theorem ClosedPost.positioned_events {before : TSO64.State}
    {inputs : Fin before.workers.length → Input} {actions : List Action}
    {actual : TSO64.State × List Observation} {offset : Nat}
    (post : ClosedPost before inputs actions actual offset) :
    post.run.events.map (fun event => (event.position, event.toSource orders)) =
      post.calls.calls.map (fun call => (offset + call.performed, call.event)) := by
  rw [post.machineEvents]
  simp only [Post.calls, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro tid _member
  exact congrArg (Prod.mk (offset + (post.calls.outcomes tid).performed))
    ((post.calls.outcomes tid).machineEvent_toSource (post.sources tid) offset)

/-- The manifest covers all live cells, including cells unused by this cohort,
and each word is the actual published initial RAM read. -/
theorem ClosedPost.initialized {before : TSO64.State}
    {inputs : Fin before.workers.length → Input} {actions : List Action}
    {actual : TSO64.State × List Observation} {offset : Nat}
    (post : ClosedPost before inputs actions actual offset) (entry : AtomicTrace.Initials.Entry) :
    entry ∈ post.initials ↔ before.world.cells entry.identifier = some entry.cell ∧
      loadQWord (published before.world) entry.cell.address = .ok entry.value :=
  AtomicTrace.Initials.enumerate_live_iff post.captured.valid.1 post.captured.enumerated entry

end EDSL.Grading.ConcurrentTask.Plain64

#audit_edsl
