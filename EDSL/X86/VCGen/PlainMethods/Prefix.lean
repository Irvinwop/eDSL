/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.PlainMethods.Completion

/-!
Construct a chosen finite prefix of the actual remaining own instructions.
The production `advance` engine establishes success; `schedule_preserves`
recovers the complete current cutpoint and actual access annotations.

The bound is the supplied point's remaining count, including zero at done.
Methods, worker contexts, incoming mixed queues and AF choices are arbitrary
under the existing Current/At contracts. No future success or reply is an
input. The preamble corollary reaches the real RET without executing it, so
distinct workers can perform their accesses before either worker returns.

This constructs finite schedules under sharedCell and the existing method
environmental assumptions. It adds no interpreter, publication, fairness,
source preservation, compiler correspondence or corpus witness claim.
-/

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.X86.VCGen.PlainMethods
open OS OS.TSO64 AtomicMethods

/-- Expose the actual first AF choice and shift the remaining own choices. -/
theorem remainingIssues_succ (tid count : Nat) (choices : Nat → Bool) :
    remainingIssues tid (count + 1) choices =
      .issue tid (choices 0) :: remainingIssues tid count (fun index => choices (index + 1)) := by
  unfold remainingIssues
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, Function.comp_def]

theorem remainingIssues_only (tid count : Nat) (choices : Nat → Bool) :
    ∀ action ∈ remainingIssues tid count choices, ∃ af, action = .issue tid af := by
  intro action member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  exact ⟨choices index, rfl⟩

theorem remainingIssues_ownIssues (tid count : Nat) (choices : Nat → Bool) :
    ownIssues tid (remainingIssues tid count choices) = count := by
  induction count generalizing choices with
  | zero => rfl
  | succ count ih =>
    rw [remainingIssues_succ]
    simp only [ownIssues, ownIssue, ite_true, ih, Nat.one_add]

/-- A partial execution retains the actual result, the actual final worker,
and complete access annotations. A retained reply is supplied by execution,
including a reply already present at a ret/done starting cutpoint. -/
structure Prefix (method : Method) (tid : Nat) (state : OS.TSO64.State)
    (point : Point method.operation) (count : Nat) (choices : Nat → Bool) where
  result : OS.TSO64.State × List Observation
  next : Point method.operation
  worker : Worker
  emissions : List (Option method.operation.Reply)
  actual : schedule state (remainingIssues tid count choices) .sharedCell = .ok result
  current : Current method result.1
  live : result.1.workers[tid]? = some worker
  located : At method next worker
  progress : next.remaining + count = point.remaining
  replies : point.replies ++ emissions.filterMap id = next.replies
  trace : AccessTrace method tid state (remainingIssues tid count choices) result emissions

private theorem prefix_scheduled {method : Method} {tid : Nat} :
    ∀ (count : Nat) (state : OS.TSO64.State) (point : Point method.operation) (worker : Worker),
      count ≤ point.remaining → Current method state → state.workers[tid]? = some worker →
      At method point worker → ∀ choices : Nat → Bool, ∃ result,
        schedule state (remainingIssues tid count choices) .sharedCell = .ok result := by
  intro count
  induction count with
  | zero =>
    intro state point worker _within _current _live _located _choices
    exact ⟨(state, []), rfl⟩
  | succ count ih =>
    intro state point worker within current live located choices
    have unfinished : point.remaining ≠ 0 := by omega
    obtain ⟨advanced⟩ := advance current live located unfinished (choices 0)
    have nextWithin : count ≤ advanced.next.remaining := by
      have progress := advanced.progress
      omega
    obtain ⟨result, scheduled⟩ := ih advanced.result.1 advanced.next advanced.worker nextWithin
      (current.step advanced.actual) advanced.live advanced.located
      (fun index => choices (index + 1))
    refine ⟨(result.1, advanced.result.2 :: result.2), ?_⟩
    rw [remainingIssues_succ]
    simp only [schedule, advanced.actual, ok_bind, scheduled, pure_ok]

/-- Execute any chosen count within the actual present remaining count.
Success follows from present authority and location, with each own AF choice
used at its specified index. Neither a future success nor a final At is a
premise. Counts zero and the complete remaining count use the same API. -/
theorem execute_prefix {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {point : Point method.operation} {worker : Worker} (current : Current method state)
    (live : state.workers[tid]? = some worker) (located : At method point worker)
    (count : Nat) (within : count ≤ point.remaining) (choices : Nat → Bool) :
    Nonempty (Prefix method tid state point count choices) := by
  obtain ⟨result, actual⟩ := prefix_scheduled count state point worker within current live located choices
  obtain ⟨finalCurrent, next, after, emissions, afterLive, afterAt, progress, replies, trace⟩ :=
    schedule_preserves current live located actual
  exact ⟨⟨result, next, after, emissions, actual, finalCurrent, afterLive, afterAt,
    by simpa only [remainingIssues_ownIssues] using progress, replies, trace⟩⟩

/-- Every peer keeps its literal worker, including its context, phase,
resources, mixed FIFO and nextStore. Current for a peer's method transports
separately by `schedule_preserves` over `execution.actual`. -/
theorem Prefix.peer {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {point : Point method.operation} {count : Nat} {choices : Nat → Bool}
    (execution : Prefix method tid state point count choices) {peer : Nat}
    (different : peer ≠ tid) :
    execution.result.1.workers[peer]? = state.workers[peer]? :=
  completion_schedule_peer (remainingIssues_only tid count choices) execution.actual different

/-- Append the constructed block to an actual prior, preserving the full
action list and every observation of both real runs in their original order. -/
theorem Prefix.append {method : Method} {tid : Nat} {initial : OS.TSO64.State}
    {prior : List Action} {actual : OS.TSO64.State × List Observation}
    {point : Point method.operation} {count : Nat} {choices : Nat → Bool}
    (execution : Prefix method tid actual.1 point count choices)
    (success : schedule initial prior .sharedCell = .ok actual) :
    schedule initial (prior ++ remainingIssues tid count choices) .sharedCell =
      .ok (execution.result.1, actual.2 ++ execution.result.2) :=
  completion_schedule_append success execution.actual

/-- Construct the block at a current cut recovered from any actual prior,
retaining its exact action/observation concatenation. The only success input
concerns the already executed prior, never the constructed block. -/
theorem prefix_after {method : Method} {tid : Nat} {initial : OS.TSO64.State}
    {prior : List Action} {actual : OS.TSO64.State × List Observation}
    (success : schedule initial prior .sharedCell = .ok actual)
    (cut : CompletionCut method tid actual.1) (count : Nat)
    (within : count ≤ cut.point.remaining) (choices : Nat → Bool) :
    ∃ execution : Prefix method tid actual.1 cut.point count choices,
      schedule initial (prior ++ remainingIssues tid count choices) .sharedCell =
        .ok (execution.result.1, actual.2 ++ execution.result.2) := by
  obtain ⟨execution⟩ := execute_prefix cut.current cut.live cut.located count within choices
  exact ⟨execution, execution.append success⟩

/-- A remaining count of one identifies the real RET stage. -/
theorem Point.remaining_one {operation : Operation} {point : Point operation}
    (one : point.remaining = 1) : ∃ offset reply, point = .ret offset reply := by
  cases point with
  | preamble offset padding =>
    simp only [Point.remaining] at one
    omega
  | ret offset reply => exact ⟨offset, reply, rfl⟩
  | done reply => cases one

/-- Run all padding and the one actual access, stopping before RET. In
particular this applies to the initial `.preamble 0 padding` cutpoint. The
reply and unique access origin come from this actual prefix, and the final
worker is still running at the decoded RET. `Prefix.peer` lets a second
worker run its own such block while this worker stays at that exact RET. -/
theorem prefix_to_ret {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {offset : Nat} {padding : List Padding} {worker : Worker} (current : Current method state)
    (live : state.workers[tid]? = some worker)
    (located : At method (.preamble offset padding) worker) (choices : Nat → Bool) :
    ∃ (execution : Prefix method tid state (.preamble offset padding) (padding.length + 1) choices)
      (retOffset : Nat) (reply : method.operation.Reply),
      execution.next = .ret retOffset reply ∧
      At method (.ret retOffset reply) execution.worker ∧
      execution.next.remaining = 1 ∧
      execution.emissions.filterMap id = [reply] ∧
      OneAccess method tid state (remainingIssues tid (padding.length + 1) choices)
        execution.result reply := by
  have within : padding.length + 1 ≤ (Point.preamble offset padding : Point method.operation).remaining := by
    simp only [Point.remaining]
    omega
  obtain ⟨execution⟩ := execute_prefix current live located (padding.length + 1) within choices
  have one : execution.next.remaining = 1 := by
    have progress := execution.progress
    change execution.next.remaining + (padding.length + 1) = padding.length + 2 at progress
    omega
  obtain ⟨retOffset, reply, next⟩ := Point.remaining_one one
  have atRet : At method (.ret retOffset reply) execution.worker := by
    rw [← next]
    exact execution.located
  have single : execution.emissions.filterMap id = [reply] := by
    have replies := execution.replies
    simpa only [Point.replies, List.nil_append, next] using replies
  exact ⟨execution, retOffset, reply, next, atRet, one, single, execution.trace.one_access single⟩

end EDSL.X86.VCGen.PlainMethods

#audit_edsl
