/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.PlainMethods.Prefix
import EDSL.X86.VCGen.PlainMethods.Positions

/-!
Construct two actual access prefixes from the original invocations at slots
0 and 1. Each block uses its own arbitrary AF function, runs the original
padding and one access, and stops at its decoded RET. The second block keeps
the first block's literal worker, so both actual final workers remain running
at their real RETs. Actions and observations concatenate in execution order.

The invocations carry the existing sharedCell method/resource/environmental
contracts, including long mode, CET off, scalar RAM, translation/aliasing and
managed caller/code/cell authority. Methods, values, padding and initial mixed
FIFOs remain arbitrary. Other worker slots may exist; no cohort coverage,
population equality, quiescence, publication, read source, history, compiler
case or corpus certificate is supplied or inferred.

The original-run annotations are retained separately from the two block
annotations. A later independent Post position bridge can use `Positions`
against its own actual full run; this module does not construct that Post.
-/

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.X86.VCGen.PlainMethods
open OS OS.TSO64 AtomicMethods

/-- The original padding and access of slot 0, followed by those of slot 1.
The AF indices are local to their respective blocks; neither block issues RET. -/
def overlapActions {before : OS.TSO64.State}
    (first : Invocation before 0) (second : Invocation before 1)
    (firstAF secondAF : Nat → Bool) : List Action :=
  remainingIssues 0 (first.padding.length + 1) firstAF ++
    remainingIssues 1 (second.padding.length + 1) secondAF

/-- A certificate for the two actual blocks and their concatenated run.
Final liveness names the literal workers produced by the two prefixes.
`firstAt` and `secondAt`, together with that liveness, are the final RET cuts.
The block OneAccess witnesses and the original-run InvocationCut annotations
all concern these actual executions, rather than a proposed future history. -/
structure Overlap {before : OS.TSO64.State}
    (first : Invocation before 0) (second : Invocation before 1)
    (firstAF secondAF : Nat → Bool) where
  firstPrefix : Prefix first.method 0 before (.preamble 0 first.padding)
    (first.padding.length + 1) firstAF
  firstOffset : Nat
  firstReply : first.method.operation.Reply
  firstNext : firstPrefix.next = .ret firstOffset firstReply
  firstAt : At first.method (.ret firstOffset firstReply) firstPrefix.worker
  firstSingle : firstPrefix.emissions.filterMap id = [firstReply]
  firstAccess : OneAccess first.method 0 before
    (remainingIssues 0 (first.padding.length + 1) firstAF) firstPrefix.result firstReply
  secondStartCurrent : Current second.method firstPrefix.result.1
  secondStartPeer : firstPrefix.result.1.workers[1]? = before.workers[1]?
  secondStartLive : firstPrefix.result.1.workers[1]? = some second.initial
  secondPrefix : Prefix second.method 1 firstPrefix.result.1 (.preamble 0 second.padding)
    (second.padding.length + 1) secondAF
  secondOffset : Nat
  secondReply : second.method.operation.Reply
  secondNext : secondPrefix.next = .ret secondOffset secondReply
  secondAt : At second.method (.ret secondOffset secondReply) secondPrefix.worker
  secondSingle : secondPrefix.emissions.filterMap id = [secondReply]
  secondAccess : OneAccess second.method 1 firstPrefix.result.1
    (remainingIssues 1 (second.padding.length + 1) secondAF) secondPrefix.result secondReply
  result : OS.TSO64.State × List Observation
  result_eq : result =
    (secondPrefix.result.1, firstPrefix.result.2 ++ secondPrefix.result.2)
  actual : schedule before (overlapActions first second firstAF secondAF) .sharedCell = .ok result
  firstFinalPeer : result.1.workers[0]? = firstPrefix.result.1.workers[0]?
  firstFinalLive : result.1.workers[0]? = some firstPrefix.worker
  secondFinalLive : result.1.workers[1]? = some secondPrefix.worker
  firstCurrent : Current first.method result.1
  secondCurrent : Current second.method result.1
  firstRunning : firstPrefix.worker.phase = .running
  secondRunning : secondPrefix.worker.phase = .running
  firstAnnotation : InvocationCut first (overlapActions first second firstAF secondAF) result
  secondAnnotation : InvocationCut second (overlapActions first second firstAF secondAF) result

/-- Construct the two blocks using only the original present invocations and
the requested own AF functions. Success, replies, final workers, final Current,
real RET locations and access annotations are outputs. No other worker needs
to be admitted, returned or absent. -/
theorem overlap_prefixes {before : OS.TSO64.State}
    (first : Invocation before 0) (second : Invocation before 1)
    (firstAF secondAF : Nat → Bool) :
    Nonempty (Overlap first second firstAF secondAF) := by
  obtain ⟨firstPrefix, firstOffset, firstReply, firstNext, firstAt,
    _firstRemaining, firstSingle, firstAccess⟩ :=
    prefix_to_ret first.current first.live first.entry firstAF
  have secondStartCurrent : Current second.method firstPrefix.result.1 :=
    (schedule_preserves second.current second.live second.entry firstPrefix.actual).1
  have secondStartPeer : firstPrefix.result.1.workers[1]? = before.workers[1]? :=
    firstPrefix.peer (Nat.succ_ne_zero 0)
  have secondStartLive : firstPrefix.result.1.workers[1]? = some second.initial :=
    secondStartPeer.trans second.live
  obtain ⟨secondPrefix, secondOffset, secondReply, secondNext, secondAt,
    _secondRemaining, secondSingle, secondAccess⟩ :=
    prefix_to_ret secondStartCurrent secondStartLive second.entry secondAF
  let result : OS.TSO64.State × List Observation :=
    (secondPrefix.result.1, firstPrefix.result.2 ++ secondPrefix.result.2)
  have actual : schedule before (overlapActions first second firstAF secondAF)
      .sharedCell = .ok result :=
    secondPrefix.append firstPrefix.actual
  have firstFinalPeer : result.1.workers[0]? = firstPrefix.result.1.workers[0]? :=
    secondPrefix.peer (Ne.symm (Nat.succ_ne_zero 0))
  have firstFinalLive : result.1.workers[0]? = some firstPrefix.worker :=
    firstFinalPeer.trans firstPrefix.live
  have firstCurrent : Current first.method result.1 :=
    (schedule_preserves firstPrefix.current firstPrefix.live firstAt secondPrefix.actual).1
  obtain ⟨firstAnnotation⟩ := first.cut_after_prefix actual
  obtain ⟨secondAnnotation⟩ := second.cut_after_prefix actual
  exact ⟨{
    firstPrefix := firstPrefix
    firstOffset := firstOffset
    firstReply := firstReply
    firstNext := firstNext
    firstAt := firstAt
    firstSingle := firstSingle
    firstAccess := firstAccess
    secondStartCurrent := secondStartCurrent
    secondStartPeer := secondStartPeer
    secondStartLive := secondStartLive
    secondPrefix := secondPrefix
    secondOffset := secondOffset
    secondReply := secondReply
    secondNext := secondNext
    secondAt := secondAt
    secondSingle := secondSingle
    secondAccess := secondAccess
    result := result
    result_eq := rfl
    actual := actual
    firstFinalPeer := firstFinalPeer
    firstFinalLive := firstFinalLive
    secondFinalLive := secondPrefix.live
    firstCurrent := firstCurrent
    secondCurrent := secondPrefix.current
    firstRunning := firstAt.location.1
    secondRunning := secondAt.location.1
    firstAnnotation := firstAnnotation
    secondAnnotation := secondAnnotation
  }⟩

/-- A final cut for slot 0 at its actual RET, ready for existing completion
APIs. Its worker is exactly the worker retained across the second block. -/
def Overlap.firstCut {before : OS.TSO64.State}
    {first : Invocation before 0} {second : Invocation before 1}
    {firstAF secondAF : Nat → Bool} (execution : Overlap first second firstAF secondAF) :
    CompletionCut first.method 0 execution.result.1 where
  point := .ret execution.firstOffset execution.firstReply
  worker := execution.firstPrefix.worker
  current := execution.firstCurrent
  live := execution.firstFinalLive
  located := execution.firstAt

/-- A final cut for slot 1 at its actual RET. No return or FIFO drain has
been added to either access block. -/
def Overlap.secondCut {before : OS.TSO64.State}
    {first : Invocation before 0} {second : Invocation before 1}
    {firstAF secondAF : Nat → Bool} (execution : Overlap first second firstAF secondAF) :
    CompletionCut second.method 1 execution.result.1 where
  point := .ret execution.secondOffset execution.secondReply
  worker := execution.secondPrefix.worker
  current := execution.secondCurrent
  live := execution.secondFinalLive
  located := execution.secondAt

end EDSL.X86.VCGen.PlainMethods

#audit_edsl
