/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.CounterCall
import EDSL.OS.TSO64.EffectSimulation.Mixed.Block
import EDSL.OS.TSO64.EffectSimulation.Mixed.Counts

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Compiler-specific increment labels for the complete, unfiltered counter log.
Every own RMW retains its actual typed checked issue, selected node and ADD or
INC tag; event arithmetic alone does not identify an instruction. An incoming
history's connected origin and initial admission remain separate obligations.

Idle transport excludes new own RMW entries through the existing native idle
count law and leaves all earlier witnesses intact. These predicates and closure
laws establish no complete-program count, completion, lifecycle, fairness,
physical LOCK or compiler-refinement claim. They inherit the native effect's
long-mode/CET-off, coherent scalar WB RAM, stable translation/no-alias and
protected-resource assumptions; they do not strengthen those assumptions.
-/

namespace EDSL.Corpus.V1.CounterCommon
open X86 OS OS.TSO64 OS.TSO64.EffectSimulation

/-- Keep the real compiler-specific arithmetic instruction family. -/
def tag : Compiler → Decoded .arithmetic
  | .defaultGCC => CounterMixedGraphs.addOne
  | .defaultClang => CounterMixedGraphs.incOne

/-- A unit arithmetic event at the independently chosen actor and target. -/
def EventOK {c : Compiler} (site : Site c) (call : Call)
    (event : Atomics64.FetchAddEvent) : Prop :=
  event.actor = site.original.resources.actor ∧
  event.cell = call.target ∧
  event.arithmetic.event.address = call.address ∧
  event.arithmetic.delta = 1 ∧
  event.arithmetic.event.after = event.arithmetic.event.before + 1

/-- Authenticate every own RMW by its actual typed checked issue and its tag.
The existential retains the machine observation, including distinct ADD/INC
flags, rather than trying to reconstruct an instruction from an event payload. -/
def OwnIncrements {c : Compiler} (site : Site c) (call : Call) (history : Log) : Prop :=
  ∀ tick ∈ history, ∀ event,
    tick.result.2 = .rmw (descriptor site call).tid event →
      EventOK site call event ∧
      ∃ af node world machine,
        tick.action = .issue (descriptor site call).tid af ∧
        ((descriptor site call).graph.node node).instruction = tag c ∧
        Mixed.AtomicIssued (descriptor site call) node tick.before af tick.result
          (world, event) machine

/-- No assertion about initial resources or future execution is needed for an
empty history. -/
theorem OwnIncrements.nil {c : Compiler} (site : Site c) (call : Call) :
    OwnIncrements site call [] := by
  intro tick member
  cases member

/-- Concatenation preserves the exact witnesses of both input histories. -/
theorem OwnIncrements.append {c : Compiler} {site : Site c} {call : Call}
    {front back : Log} (first : OwnIncrements site call front)
    (second : OwnIncrements site call back) :
    OwnIncrements site call (front ++ back) := by
  intro tick member event observed
  rcases List.mem_append.mp member with old | new
  · exact first tick old event observed
  · exact second tick new event observed

/-- An ordinary issue contributes its full scheduler position without an RMW. -/
theorem OwnIncrements.snoc_ordinary {c : Compiler} {site : Site c} {call : Call}
    {history : Log} (prior : OwnIncrements site call history)
    (before after : S) (af : Bool) :
    OwnIncrements site call
      (Mixed.issueLog (descriptor site call) before history af
        (after, .ordinary (descriptor site call).tid)) := by
  intro tick member event observed
  rcases List.mem_append.mp member with old | new
  · exact prior tick old event observed
  · have same := List.mem_singleton.mp new
    subst tick
    cases observed

/-- RET contributes its actual returned position without an RMW. -/
theorem OwnIncrements.snoc_returned {c : Compiler} {site : Site c} {call : Call}
    {history : Log} (prior : OwnIncrements site call history)
    (before after : S) (af : Bool) :
    OwnIncrements site call
      (Mixed.issueLog (descriptor site call) before history af
        (after, .returned (descriptor site call).tid)) := by
  intro tick member event observed
  rcases List.mem_append.mp member with old | new
  · exact prior tick old event observed
  · have same := List.mem_singleton.mp new
    subst tick
    cases observed

/-- Only the supplied current checked issue authenticates the appended RMW.
Its full machine observation and exact compiler-specific tag remain available. -/
theorem OwnIncrements.snoc_increment {c : Compiler} {site : Site c} {call : Call}
    {history : Log} {before after : S} {af : Bool}
    {node : (descriptor site call).graph.Index} {world : World}
    {event : Atomics64.FetchAddEvent} {machine : AddRMW64.Observation}
    (prior : OwnIncrements site call history)
    (selected : ((descriptor site call).graph.node node).instruction = tag c)
    (eventOK : EventOK site call event)
    (issued : Mixed.AtomicIssued (descriptor site call) node before af
      (after, .rmw (descriptor site call).tid event) (world, event) machine) :
    OwnIncrements site call
      (Mixed.issueLog (descriptor site call) before history af
        (after, .rmw (descriptor site call).tid event)) := by
  intro tick member nextEvent observed
  rcases List.mem_append.mp member with old | new
  · exact prior tick old nextEvent observed
  · have same := List.mem_singleton.mp new
    subst tick
    have eventSame : event = nextEvent := by
      cases observed
      rfl
    subst nextEvent
    exact ⟨eventOK, af, node, world, machine, rfl, selected, issued⟩

/-- An authenticated idle suffix cannot contain a new own RMW. Prefix
witnesses need no reinterpretation in the final world. -/
theorem OwnIncrements.idle {c : Compiler} {site : Site c} {call : Call}
    {before after : S} {history extended : Log}
    (idle : Mixed.Idle (descriptor site call).profile (descriptor site call).tid
      (before, history) (after, extended) (descriptor site call).family)
    (prior : OwnIncrements site call history) :
    OwnIncrements site call extended := by
  obtain ⟨suffix, _trace, allowed, same⟩ := idle
  change extended = history ++ suffix at same
  rw [same]
  intro tick member event observed
  rcases List.mem_append.mp member with old | new
  · exact prior tick old event observed
  · have zero := Mixed.Counts.idleStep_zero (allowed tick new)
    rw [observed, Mixed.Counts.ownRMW_rmw, ite_eq_left rfl] at zero
    cases zero

#print axioms tag
#print axioms EventOK
#print axioms OwnIncrements
#print axioms OwnIncrements.nil
#print axioms OwnIncrements.append
#print axioms OwnIncrements.snoc_ordinary
#print axioms OwnIncrements.snoc_returned
#print axioms OwnIncrements.snoc_increment
#print axioms OwnIncrements.idle

end EDSL.Corpus.V1.CounterCommon

#audit_edsl
